module Examples.ConferenceManager

import DepSec.DIO
import DepSec.Labeled
import DepSec.Ref

import Examples.ConferenceLattice

%default total

-- Examples derived from "Luísa Lourenço and Luís Caires. 2015.
-- Dependent Information Flow Types (POPL '15)"

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------
record User where
  constructor MkUser
  uid   : Uid
  name  : Labeled (U uid) String
  univ  : Labeled (U uid) String
  email : Labeled (U uid) String

record Submission where
  constructor MkSubmission
  uid   : Uid
  sid   : Sid
  title : Labeled (A uid sid) String
  abs   : Labeled (A uid sid) String
  paper : Labeled (A uid sid) String

record Review where
  constructor MkReview
  uid     : Uid
  sid     : Sid
  PC_only : Labeled (PC uid sid) String
  review  : Labeled (A Top sid) String
  grade   : Labeled (A Top sid) Integer

Bot' : Compartment
Bot' = Bottom

Users : Type
Users = SecRef Bot' (List (SecRef Bot' User))

Submissions : Type
Submissions = SecRef Bot' (List (SecRef Bot' Submission))

Reviews : Type
Reviews = SecRef Bot' (List (SecRef Bot' Review))

--------------------------------------------------------------------------------
-- Hints
--------------------------------------------------------------------------------
%hint
botFlowsToBot : Bot' `leq` Bot'
botFlowsToBot = reflexive Bot'

implicit
stringToLabeled : Poset labelType => {l : labelType} -> String -> Labeled l String
stringToLabeled = label

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

-- Example 2.1
assignReviewer : Reviews -> Uid -> Sid -> DIO Bot' ()
assignReviewer revRef uid1 sid1 =
  do reviews <- unlabel !(readRef revRef)
     new <- (newRef {l = Bot'} {l' = Bot'} {l'' = Bot'} (label (MkReview uid1 sid1 "" "" (label 0))))
     let newreviews = label (new :: reviews)
     writeRef {l = Bot'} {l' = Bot'} {l'' = Bot'} revRef newreviews

-- Example 2.2
viewAuthorPapers : Submissions
                -> (uid1 : Uid)
                -> DIO Bot' (List (sub : Submission ** uid1 = (uid sub)))
viewAuthorPapers subRef uid1 =
  do submissions <- unlabel !(readRef subRef)
     findPapers submissions
  where
    findPapers : (List (SecRef Bot' Submission))
              -> DIO Bot' (List (sub : Submission ** uid1 = (uid sub)))
    findPapers [] = pure []
    findPapers (x :: xs) =
      do sub <- unlabel !(readRef x)
         case decEq (uid sub) uid1 of
           (Yes prf) => pure $ (sub ** (sym prf)) :: !(findPapers xs)
           (No _) => findPapers xs


-- Example 2.3
viewAssignedPapers : Reviews -> Submissions -> Uid -> DIO Bot' (List (SecRef Bot' Submission))
viewAssignedPapers reviewsRef subsRef id =
  do reviews <- unlabel !(readRef reviewsRef)
     subs <- unlabel !(readRef subsRef)
     sids <- getSids reviews
     findPapers sids subs
  where
  getSids : List (SecRef (U Bot) Review) -> DIO Bot' $ List Sid
  getSids [] = pure []
  getSids (x :: xs) =
    do rev <- unlabel !(readRef x)
       case decEq (uid rev) id of
         (Yes _) => pure $ (sid rev) :: !(getSids xs)
         (No _) => getSids xs

  findPapers : List Sid -> List (SecRef Bot' Submission) -> DIO Bot' (List (SecRef Bot' Submission))
  findPapers xs [] = pure []
  findPapers xs (x :: ys) =
    do sub <- unlabel !(readRef x)
       case elemBy (==) (sid sub) xs of
         True => pure $ x :: !(findPapers xs ys)
         False => findPapers xs ys

-- Example 2.4
emphasizeTitle : Uid -> Sid -> Submissions -> DIO Bot' ()
emphasizeTitle uid1 sid1 subsRef =
  do subs <- unlabel !(readRef subsRef)
     ltitle <- getTitleOfSub subs
     lNewTitle <- appendToTitle "!" ltitle
     searchAndReplaceTitle lNewTitle subs
     pure ()
  where
  searchAndReplaceTitle : Labeled (A uid1 sid1) String -> List (SecRef Bot' Submission) -> DIO Bot' ()
  searchAndReplaceTitle newTitle [] = pure ()
  searchAndReplaceTitle newTitle (x :: xs) =
    do sub <- unlabel !(readRef x)
       case (decEq (uid sub) uid1, decEq (sid sub) sid1) of
         (Yes prf1, Yes prf2) =>
           let abs'= abs sub
               paper' = paper sub
               title' : Labeled (A (uid sub) (sid sub)) String =
                 rewrite prf1 in
                 rewrite prf2 in
                 newTitle
               newSub = MkSubmission (uid sub) (sid sub) title' abs' paper'
               newlsub : Labeled Bot' Submission = label newSub
           in writeRef {l = Bot'} {l' = Bot'} {l'' = Bot'} x newlsub
         (_ , _ ) => searchAndReplaceTitle newTitle xs

  getTitleOfSub : List (SecRef Bot' Submission) -> DIO Bot' (Labeled (A uid1 sid1) String)
  getTitleOfSub [] = pure ""
  getTitleOfSub (x :: xs) =
    do sub <- unlabel !(readRef x)
       case (decEq (uid sub) uid1, decEq (sid sub) sid1) of
         (Yes prf1, Yes prf2) =>
           rewrite sym $ prf1 in
           rewrite sym $ prf2 in
           pure $ title sub
         (_,_) => getTitleOfSub xs

  appendToTitle : String -> Labeled (A x y) String -> DIO Bot' (Labeled (A x y) String)
  appendToTitle {x} {y} str lstr =
    do let oldStrDIO : DIO (A x y) String = unlabel {flow = reflexive (A x y)} lstr
       let newStrDIO : DIO (A x y) String = do pure $ (!oldStrDIO ++ str)
       plug newStrDIO

-- Example 2.5
addCommentSubmission : Reviews
                    -> (uid1 : Uid)
                    -> (sid1 : Sid)
                    -> (comment : Labeled (A uid1 sid1) String)
                    -> DIO Bot' ()
addCommentSubmission revsRef uid1 sid1 comment =
  do revs <- unlabel !(readRef revsRef)
     addComment revs
  where
  addComment : List (SecRef (U Bot) Review) -> DIO Bot' ()
  addComment [] = pure ()
  addComment (x :: xs) =
    do rev <- unlabel !(readRef x)
       case (decEq (uid rev) uid1, decEq (sid rev) sid1) of
         (Yes prf1, Yes prf2) =>
           let review' = review rev
               grade' = grade rev
               PC_only' : Labeled (PC (uid rev) (sid rev)) String =
                 rewrite prf1 in
                 rewrite prf2 in relabel {flow=A_leq_PC {uid1}} comment
               newRev = MkReview (uid rev) (sid rev) PC_only' review' grade'
               newlRev : Labeled Bot' Review = label newRev
           in writeRef {l = Bot'} {l' = Bot'} {l'' = Bot'} x newlRev
         _ => addComment xs

--------------------------------------------------------------------------------
-- Test data
--------------------------------------------------------------------------------

User1 : User
User1 = MkUser (Nat 1) "Alice" "Foo University" "alice@cs.foo.dk"

User2 : User
User2 = MkUser (Nat 2) "Bob" "Bar University" "bob@cs.bar.dk"

User3 : User
User3 = MkUser (Nat 3) "Chuck" "Baz University" "chuck@cs.baz.dk"

Paper1 : Submission
Paper1 = MkSubmission (Nat 1) (Nat 1) "IFC in Idris" "Dependent types seems good?" "QED"

Paper2 : Submission
Paper2 = MkSubmission (Nat 2) (Nat 2) "Haskell is old fashioned" "Why not more Idris?" "QED"

Paper3 : Submission
Paper3 = MkSubmission (Nat 1) (Nat 3) "Messing with Idris" "Idris is fun!" "QED"

Review1 : Review
Review1 = MkReview (Nat 3) (Nat 1) "Pretty good" "That's okay" (label 12)

Review2 : Review
Review2 = MkReview (Nat 3) (Nat 2) "Yay!" "OK!" (label 12)

initUsers : DIO Bot' Users
initUsers = newRef {flow=reflexive Bot'} {flow'=reflexive Bot'} (label Nil)

initSubmissions : DIO Bot' Submissions
initSubmissions = newRef (label Nil)

initReviews : DIO Bot' Reviews
initReviews = newRef {flow=reflexive Bot'} {flow'=reflexive Bot'} (label Nil)

dummyDB : Users -> Submissions -> Reviews -> DIO Bot' ()
dummyDB users submissions reviews=
  do user1 <- newRef {l = Bot'} {l' = Bot'} {l'' = Bot'} (label User1)
     user2 <- newRef {l = Bot'} {l' = Bot'} {l'' = Bot'} (label User2)
     let newusers = label {l=Bot'} [user1, user2]
     writeRef {l = Bot'} {l' = Bot'} {l'' = Bot'} users newusers

     sub1 <- newRef {l = Bot'} {l' = Bot'} {l'' = Bot'} (label Paper1)
     sub2 <- newRef {l = Bot'} {l' = Bot'} {l'' = Bot'} (label Paper2)
     sub3 <- newRef {l = Bot'} {l' = Bot'} {l'' = Bot'} (label Paper3)
     let newsubmissions = label {l=Bot'} [sub1, sub2, sub3]
     writeRef {l = Bot'} {l' = Bot'} {l'' = Bot'} submissions newsubmissions

     rev1 <- newRef {l = Bot'} {l' = Bot'} {l'' = Bot'} (label Review1)
     rev2 <- newRef {l = Bot'} {l' = Bot'} {l'' = Bot'} (label Review2)
     let newreviews = label {l=Bot'} [rev1, rev2]
     writeRef {l = Bot'} {l' = Bot'} {l'' = Bot'} reviews newreviews

--------------------------------------------------------------------------------
-- Main
--------------------------------------------------------------------------------
main : IO ()
main =
  do putStrLn "Starting conference manager ..."
     run $
       do users <- initUsers
          submissions <- initSubmissions
          reviews <- initReviews
          dummyDB users submissions reviews

          assignReviewer reviews (Nat 42) (Nat 1)
          addCommentSubmission reviews (Nat 2) (Nat 2) "Cool paper!"

          reviews' <- unlabel !(readRef reviews)
          lift $ putStrLn $ "No. of reviews: " ++ (cast $ length reviews')

          alice <- viewAuthorPapers submissions (Nat 1)
          lift $ putStrLn $ "No. of submissions from Alice: " ++ (cast $ length alice)

          papersToReview <- viewAssignedPapers reviews submissions (Nat 3)
          lift $ putStrLn $ "No. of papers to review Chuck: " ++ (cast $ length papersToReview)

          pure ()
     putStrLn "Shutting down conference manager ..."
