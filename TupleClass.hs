{-# LANGUAGE
      FlexibleContexts,
      FlexibleInstances,
      TypeFamilies,
      UnicodeSyntax
  #-}

module TupleClass  where

import Control.Applicative

class Tuple tup where
  type HeadT tup
  type TailT tup
  type InitT tup
  type LastT tup
  type RevT  tup
  headT    ∷ tup → HeadT tup
  tailT    ∷ tup → TailT tup
  initT    ∷ tup → InitT tup
  lastT    ∷ tup → LastT tup
  consT    ∷ HeadT tup → TailT tup → tup
  snocT    ∷ InitT tup → LastT tup → tup
  revT     ∷ tup → RevT tup
  --
  revRevLaw   ∷ (RevT (RevT tup) ~ tup) ⇒ tup → tup

instance Tuple (a,b) where
  type HeadT (a,b)  = a
  type TailT (a,b)  = b
  type InitT (a,b)  = a
  type LastT (a,b)  = b
  type RevT  (a,b)  = (b,a)
  headT = fst
  tailT = snd
  initT = fst
  lastT = snd
  consT = (,)
  snocT = (,)
  revT  = (,) <$> snd <*> fst
  revRevLaw = id

instance Tuple (a,b,c) where
  type HeadT (a,b,c) = a
  type TailT (a,b,c) = (b,c)
  type InitT (a,b,c) = (a,b)
  type LastT (a,b,c) = c
  type RevT (a,b,c)  = (c,b,a)
  headT (x,_,_) = x
  tailT (_,y,z) = (y,z)
  initT (x,y,_) = (x,y)
  lastT (_,_,z) = z
  consT x (y,z) = (x,y,z)
  snocT (x,y) z = (x,y,z)
  revT (x,y,z)  = (z,y,x)
  revRevLaw = id

instance Tuple (a,b,c,d) where
  type HeadT (a,b,c,d) = a
  type TailT (a,b,c,d) = (b,c,d)
  type InitT (a,b,c,d) = (a,b,c)
  type LastT (a,b,c,d) = d
  type RevT (a,b,c,d)  = (d,c,b,a)
  headT (x,_,_,_) = x
  tailT (_,y,z,w) = (y,z,w)
  initT (x,y,z,_) = (x,y,z)
  lastT (_,_,_,w) = w
  consT x (y,z,w) = (x,y,z,w)
  snocT (x,y,z) w = (x,y,z,w)
  revT (x,y,z,w)  = (w,z,y,x)
  revRevLaw = id

instance Tuple (a,b,c,d,e) where
  type HeadT (a,b,c,d,e) = a
  type TailT (a,b,c,d,e) = (b,c,d,e)
  type InitT (a,b,c,d,e) = (a,b,c,d)
  type LastT (a,b,c,d,e) = e
  type RevT (a,b,c,d,e)  = (e,d,c,b,a)
  headT (x,_,_,_,_) = x
  tailT (_,y,z,w,v) = (y,z,w,v)
  initT (x,y,z,w,_) = (x,y,z,w)
  lastT (_,_,_,_,v) = v
  consT x (y,z,w,v) = (x,y,z,w,v)
  snocT (x,y,z,w) v = (x,y,z,w,v)
  revT (x,y,z,w,v)  = (v,w,z,y,x)
  revRevLaw = id

instance Tuple (a,b,c,d,e,f) where
  type HeadT (a,b,c,d,e,f) = a
  type TailT (a,b,c,d,e,f) = (b,c,d,e,f)
  type InitT (a,b,c,d,e,f) = (a,b,c,d,e)
  type LastT (a,b,c,d,e,f) = f
  type RevT (a,b,c,d,e,f)  = (f,e,d,c,b,a)
  headT (x,_,_,_,_,_) = x
  tailT (_,y,z,w,v,u) = (y,z,w,v,u)
  initT (x,y,z,w,v,_) = (x,y,z,w,v)
  lastT (_,_,_,_,_,u) = u
  consT x (y,z,w,v,u) = (x,y,z,w,v,u)
  snocT (x,y,z,w,v) u = (x,y,z,w,v,u)
  revT (x,y,z,w,v,u)  = (u,v,w,z,y,x)
  revRevLaw = id

instance Tuple (a,b,c,d,e,f,g) where
  type HeadT (a,b,c,d,e,f,g) = a
  type TailT (a,b,c,d,e,f,g) = (b,c,d,e,f,g)
  type InitT (a,b,c,d,e,f,g) = (a,b,c,d,e,f)
  type LastT (a,b,c,d,e,f,g) = g
  type RevT (a,b,c,d,e,f,g)  = (g,f,e,d,c,b,a)
  headT (x,_,_,_,_,_,_) = x
  tailT (_,y,z,w,v,u,t) = (y,z,w,v,u,t)
  initT (x,y,z,w,v,u,_) = (x,y,z,w,v,u)
  lastT (_,_,_,_,_,_,t) = t
  consT x (y,z,w,v,u,t) = (x,y,z,w,v,u,t)
  snocT (x,y,z,w,v,u) t = (x,y,z,w,v,u,t)
  revT (x,y,z,w,v,u,t)  = (t,u,v,w,z,y,x)
  revRevLaw = id

type Prj1 tup = HeadT tup

class Tuple tup ⇒ Has1 tup where
  prj1 ∷ tup → Prj1 tup
  prj1 = headT

instance Has1 (a,b)
instance Has1 (a,b,c)
instance Has1 (a,b,c,d)
instance Has1 (a,b,c,d,e)
instance Has1 (a,b,c,d,e,f)
instance Has1 (a,b,c,d,e,f,g)

type Drp1 tup = TailT tup

class (Tuple tup, Has1 tup) ⇒ Has2 tup where
  type Prj2 tup
  prj2 ∷ tup → Prj2 tup
  drp1 ∷ tup → Drp1 tup
  drp1 = tailT

instance Has2 (a,b) where
  type Prj2 (a,b) = b
  prj2 = lastT

instance Has2 (a,b,c) where
  type Prj2 (a,b,c) = b
  prj2 = headT . drp1

instance Has2 (a,b,c,d) where
  type Prj2 (a,b,c,d) = b
  prj2 = headT . drp1

instance Has2 (a,b,c,d,e) where
  type Prj2 (a,b,c,d,e) = b
  prj2 = headT . drp1

instance Has2 (a,b,c,d,e,f) where
  type Prj2 (a,b,c,d,e,f) = b
  prj2 = headT . drp1

instance Has2 (a,b,c,d,e,f,g) where
  type Prj2 (a,b,c,d,e,f,g) = b
  prj2 = headT . drp1

type Drp2 a = TailT (Drp1 a)

class (Has2 tup, Has2 (TailT tup)) ⇒ Has3 tup where
  type Prj3 tup
  prj3 ∷ tup → Prj3 tup
  drp2 ∷ tup → Drp2 tup
  drp2 = tailT . drp1

instance Has3 (a,b,c) where
  type Prj3 (a,b,c) = c
  prj3 = lastT

instance Has3 (a,b,c,d) where
  type Prj3 (a,b,c,d) = c
  prj3 = headT . drp2

instance Has3 (a,b,c,d,e) where
  type Prj3 (a,b,c,d,e) = c
  prj3 = headT . drp2

instance Has3 (a,b,c,d,e,f) where
  type Prj3 (a,b,c,d,e,f) = c
  prj3 = headT . drp2

instance Has3 (a,b,c,d,e,f,g) where
  type Prj3 (a,b,c,d,e,f,g) = c
  prj3 = headT . drp2

type Drp3 a = TailT (Drp2 a)

class (Has3 tup, Has3 (TailT tup)) ⇒ Has4 tup where
  type Prj4 tup
  prj4 ∷ tup → Prj4 tup
  drp3 ∷ tup → Drp3 tup
  drp3 = tailT . drp2

instance Has4 (a,b,c,d) where
  type Prj4 (a,b,c,d) = d
  prj4 = lastT

instance Has4 (a,b,c,d,e) where
  type Prj4 (a,b,c,d,e) = d
  prj4 = headT . drp3

instance Has4 (a,b,c,d,e,f) where
  type Prj4 (a,b,c,d,e,f) = d
  prj4 = headT . drp3

instance Has4 (a,b,c,d,e,f,g) where
  type Prj4 (a,b,c,d,e,f,g) = d
  prj4 = headT . drp3

type Drp4 a = TailT (Drp3 a)

class (Has4 tup, Has4 (TailT tup)) ⇒ Has5 tup where
  type Prj5 tup
  prj5 ∷ tup → Prj5 tup
  drp4 ∷ tup → Drp4 tup
  drp4 = tailT . drp3

instance Has5 (a,b,c,d,e) where
  type Prj5 (a,b,c,d,e) = e
  prj5 = lastT

instance Has5 (a,b,c,d,e,f) where
  type Prj5 (a,b,c,d,e,f) = e
  prj5 = headT . drp4

instance Has5 (a,b,c,d,e,f,g) where
  type Prj5 (a,b,c,d,e,f,g) = e
  prj5 = headT . drp4

type Drp5 a = TailT (Drp4 a)

class (Has5 tup, Has5 (TailT tup)) ⇒ Has6 tup where
  type Prj6 tup
  prj6 ∷ tup → Prj6 tup
  drp5 ∷ tup → Drp5 tup
  drp5 = tailT . drp4

instance Has6 (a,b,c,d,e,f) where
  type Prj6 (a,b,c,d,e,f) = f
  prj6 = lastT

instance Has6 (a,b,c,d,e,f,g) where
  type Prj6 (a,b,c,d,e,f,g) = f
  prj6 = headT . drp5

type Drp6 a = TailT (Drp5 a)

class (Has6 tup, Has6 (TailT tup)) ⇒ Has7 tup where
  type Prj7 tup
  prj7 ∷ tup → Prj7 tup
  drp6 ∷ tup → Drp6 tup
  drp6 = tailT . drp5

instance Has7 (a,b,c,d,e,f,g) where
  type Prj7 (a,b,c,d,e,f,g) = g
  prj7 = lastT
