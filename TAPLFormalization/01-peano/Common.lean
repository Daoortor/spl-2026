import Mathlib.Logic.Relation

inductive ReflTransGen' (r : α → α → Prop) : α → α → Prop
  | refl : ReflTransGen' r a a
  | tail : r a b → ReflTransGen' r b c → ReflTransGen' r a c

lemma ReflTransGen'.single (h : r a b) : ReflTransGen' r a b := .tail h .refl

theorem ReflTransGen'.trans (hab : ReflTransGen' r a b) (hbc : ReflTransGen' r b c) :
  ReflTransGen' r a c := by
  induction hab with
  | refl => assumption
  | tail r rs ih => exact tail r (ih hbc)

theorem ReflTransGen'.trans' (hab : ReflTransGen' r a b) (hbc : r b c) :
  ReflTransGen' r a c := trans hab (.single hbc)

instance : Trans r r (ReflTransGen' r) where
  trans r₁ r₂ := .tail r₁ (.single r₂)

instance : Trans (ReflTransGen' r) (ReflTransGen' r) (ReflTransGen' r) where
  trans := ReflTransGen'.trans

instance : Trans r (ReflTransGen' r) (ReflTransGen' r) where
  trans r rs := .tail r rs

instance : Trans (ReflTransGen' r) r (ReflTransGen' r) where
  trans := ReflTransGen'.trans'

theorem ReflTransGen'.lift (f : α → β) (h : ∀ {a b}, r a b → p (f a) (f b))
  (hab : ReflTransGen' r a b) : ReflTransGen' p (f a) (f b) := by
  induction hab with
  | refl => constructor
  | tail r rs ih => exact .tail (h r) ih
