data Bool = False | True

data Ordering = LT | EQ | GT

class Ord a :: * where
  compare :: a -> a -> Ordering

data Color = Red | Black -- Color of Red-Black-Tree nodes

data Tree (a :: *) = Leaf | Node Color a (Tree a) (Tree a) -- Red-Black-Tree: Node node-color node-value left-subtree right-subtree

empty :: forall (a :: *). -- empty tree
         Tree a
       = Leaf

member :: forall (a :: *). -- element in tree
          Ord a =>
          a -> Tree a -> Bool
        = \x.\t. case t of
                   Leaf                    -> False
                   Node col top left right -> case compare x top of
                                                EQ -> True
                                                LT -> member x left
                                                GT -> member x right

reverseTree :: forall (a :: *). -- get the dual tree (tree with dual order, used to avoid repetition in function "correct")
               Tree a -> Tree a
             = \t. case t of
                     Leaf                    -> Leaf
                     Node col top left right -> Node col top right left

data Flow (a :: *) (b :: *) = Input a | Output b -- Support for more complex guards: represents a result in a stream of alternatives where either no alternaive applied (Input) or an earlier alternative did apply (Output)

correct :: forall (a :: *). -- transforms a tree (resulting from applying the function "insert'" to its left subtree) to one that agrees with the invariants of Red-Black-Trees (this is the main algorithm of insertion), we assume insertion happened in the left subtree to avoid symmetry (otherwise, we wok with the tree's dual)
           Tree a -> Tree a
         = let flow = \f.\x. case x of -- Models alternatives/guards
                               Input  y -> f y
                               Output y -> Output y
           in let case1 = \t. case t of
                                Node pcol ptop pleft pright ->
                                  case pleft of
                                    Node ncol ntop nleft nright ->
                                      case ncol of
                                        Red ->
                                          case nleft of
                                            Leaf ->
                                              case nright of
                                                Leaf -> Output t
                                                Node c a l r -> Input t
                                            Node c a l r -> Input t
                                        Black -> Input t
                                    Leaf -> Input t
                                Leaf -> Input t
           in let case2 = \t. case t of
                                Node pcol ptop pleft pright ->
                                  case pleft of
                                    Node ncol ntop nleft nright ->
                                      case ncol of
                                        Red ->
                                          case nleft of
                                            Node c1col c1top c1left c1right ->
                                              case c1col of
                                                Black ->
                                                  case nright of
                                                    Node c2col c2top c2left c2right ->
                                                      case c2col of
                                                        Black -> Output t
                                                        Red -> Input t
                                                    Leaf -> Input t
                                                Red -> Input t
                                            Leaf -> Input t
                                        Black -> Input t
                                    Leaf -> Input t
                                Leaf -> Input t
           in let case3 = \t. case t of
                                Node pcol ptop pleft pright ->
                                  case pleft of
                                    Node ncol ntop nleft nright ->
                                      case ncol of
                                        Black -> Output t
                                        Red -> Input t
                                    Leaf -> Input t
                                Leaf -> Input t
           in let case4 = \t. case t of
                                Node gcol gtop gleft gright ->
                                  case gcol of
                                    Black ->
                                      case gleft of
                                        Node pcol ptop pleft pright ->
                                          case pcol of
                                            Red ->
                                              case gright of
                                                Node ucol utop uleft uright ->
                                                  case ucol of
                                                    Red -> Output (Node Red gtop (Node Black ptop pleft pright) (Node Black utop uleft uright))
                                                    Black -> Input t
                                                Leaf -> Input t
                                            Black -> Input t
                                        Leaf -> Input t
                                    Red -> Input t
                                Leaf -> Input t
           in let case5 = \t. case t of
                                Node gcol gtop gleft gright ->
                                  case gcol of
                                    Black ->
                                      case gleft of
                                        Node pcol ptop pleft pright ->
                                          case pcol of
                                            Red ->
                                              case pright of
                                                Node ncol ntop nleft nright ->
                                                  case ncol of
                                                    Red -> Output (correct (Node Black gtop (Node Red ntop (Node Red ptop pleft nleft) nright) gright))
                                                    Black -> Input t
                                                Leaf -> Input t
                                            Black -> Input t
                                        Leaf -> Input t
                                    Red -> Input t
                                Leaf -> Input t
           in let case6 = \t. case t of
                                Node gcol gtop gleft gright ->
                                  case gcol of
                                    Black ->
                                      case gleft of
                                        Node pcol ptop pleft pright ->
                                          case pcol of
                                            Red ->
                                              case pleft of
                                                Node ncol ntop nleft nright ->
                                                  case ncol of
                                                    Red -> Output (Node Black ptop (Node Red ntop nleft nright) (Node Red gtop pright gright))
                                                    Black -> Input t
                                                Leaf -> Input t
                                            Black -> Input t
                                        Leaf -> Input t
                                    Red -> Input t
                                Leaf -> Input t
           in  \t. case flow case6 (flow case5 (flow case4 (flow case3 (flow case2 (flow case1 (Input t)))))) of
                     Output r -> r

insert' :: forall (a :: *). -- insert an element into a tree, ignoring the invariant that the top must be black
           Ord a =>
           a -> Tree a -> Tree a
         = \x.\t. case t of
                    Leaf                    -> Node Red x Leaf Leaf
                    Node col top left right -> case compare x top of
                                                 EQ -> t
                                                 LT -> correct (Node col top (insert' x left) right)
                                                 GT -> reverseTree (correct (reverseTree (Node col top left (insert' x right))))

insert :: forall (a :: *). -- insert an element into a tree, respecting all invariants of Red-Black-Trees
          Ord a =>
          a -> Tree a -> Tree a
        = \x.\t. case insert' x t of
                   Node col top left right -> Node Black top left right

data Float = F1 | F2 | F3 | F4 | F5 | NaN -- Subset of floating point numbers: 1.0, 2.0, 3.0, 4.0, 5.0 and "Not a Number"

instance Ord Float where
  compare = \x.\y. case x of
                    F1 ->  case y of
                             F1  -> EQ
                             F2  -> LT
                             F3  -> LT
                             F4  -> LT
                             F5  -> LT
                             NaN -> GT
                    F2 ->  case y of
                             F1  -> GT
                             F2  -> EQ
                             F3  -> LT
                             F4  -> LT
                             F5  -> LT
                             NaN -> GT
                    F3 ->  case y of
                             F1  -> GT
                             F2  -> GT
                             F3  -> EQ
                             F4  -> LT
                             F5  -> LT
                             NaN -> GT
                    F4 ->  case y of
                             F1  -> GT
                             F2  -> GT
                             F3  -> GT
                             F4  -> EQ
                             F5  -> LT
                             NaN -> GT
                    F5 ->  case y of
                             F1  -> GT
                             F2  -> GT
                             F3  -> GT
                             F4  -> GT
                             F5  -> EQ
                             NaN -> GT
                    NaN -> GT

data Maybe (a :: *) = Nothing | Just a

maybe :: forall (a :: *).
         forall (b :: *).
         b -> (a -> b) -> Maybe a -> b
       = \b.\f.\x. case x of
                     Nothing -> b
                     Just a  -> f a

id :: forall (a :: *).
      a -> a
    = \x.x

lessThan :: forall (a :: *). -- x < y
            Ord a =>
            a -> a -> Bool
          = \x.\y. case compare x y of
                     LT -> True
                     EQ -> False
                     GT -> False

rightmost :: forall (a :: *). -- the rightmost bottom (largest) element of a tree
             Ord a =>
             Tree a -> Maybe a
           = \t. case t of
                   Leaf -> Nothing
                   Node col top left right -> Just (maybe top id (rightmost right))

leftmost :: forall (a :: *). -- the leftmost bottom (smallest) element of a tree
            Ord a =>
            Tree a -> Maybe a
          = \t. case t of
                  Leaf -> Nothing
                  Node col top left right -> Just (maybe top id (leftmost left))

issortedAscending :: forall (a :: *). -- is the tree sorted in asceding order?
                     Ord a =>
                     Tree a -> Bool
                   = \t. case t of
                           Leaf -> True
                           Node col top left right ->
                             case maybe True (\x. lessThan x top) (rightmost left) of
                               False -> False
                               True  -> case maybe True (\x. lessThan top x) (leftmost right) of
                                          False -> False
                                          True  -> case issortedAscending left of
                                                     False -> False
                                                     True  -> issortedAscending right

issortedDescending :: forall (a :: *). -- is the tree sorted in descending order?
                      Ord a =>
                      Tree a -> Bool
                    = \t. case t of
                            Leaf -> True
                            Node col top left right ->
                              case maybe True (\x. lessThan top x) (rightmost left) of
                                False -> False
                                True  -> case maybe True (\x. lessThan x top) (leftmost right) of
                                           False -> False
                                           True  -> case issortedDescending left of
                                                      False -> False
                                                      True  -> issortedDescending right

issortedAsEither :: forall (a :: *). -- is the tree sorted in either ascending or descending order?
                    Ord a =>
                    Tree a -> Bool
                  = \t. case issortedAscending t of
                          True  -> True
                          False -> issortedDescending t

-- main = foldr insert empty [5.0, 4.0, 1.0, 3.0, 2.0]
(let e5 = F5
 in let e4 = F4
    in let e3 = F1
       in let e2 = F3
          in let e1 = F2
             in insert e5 (insert e4 (insert e3 (insert e2 (insert e1 empty)))))
