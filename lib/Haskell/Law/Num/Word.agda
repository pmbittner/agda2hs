module Haskell.Law.Num.Word where

open import Haskell.Prim
open import Haskell.Prim.Function
open import Haskell.Prim.Num
open import Haskell.Prim.Word

open import Haskell.Law.Num
open import Haskell.Law.Equality
open import Haskell.Law.Function

open Num iNumNat  renaming (_+_ to _+ⁿ_; _*_ to _*ⁿ_)
open Num iNumWord renaming (_+_ to _+ʷ_; _*_ to _*ʷ_)

postulate
  -- This is a reasonable axiom because there are more natural numbers than
  -- integer. More precisely, Words denote a finite subset of Integers.
  -- This means, there is am embedding of Words into Integers as stated by
  -- this axiom.
  n2w∘w2n≡id : ∀ (x : Word) → n2w (w2n x) ≡ x

  -- Definitions of word arithmetics are based on conversions to Nats.
  -- That conversion must be homomorphic w.r.t. to addition and multiplication
  -- to not break their properties.
  w2n-+-hom : Homomorphism₂ _+ʷ_ _+ⁿ_ w2n
  w2n-*-hom : Homomorphism₂ _*ʷ_ _*ⁿ_ w2n

  -- There also exists the following axiom, which have not yet made use of.
  -- open import Agda.Builtin.Word.Properties renaming (primWord64ToNatInjective to w2n-injective)

open MonoidEmbedding₂

+-wordsAsNats : MonoidEmbedding₂ addWord addNat w2n n2w 0 0
Embedding₂.hom   (embedding +-wordsAsNats) = w2n-+-hom
Embedding₂.embed (embedding +-wordsAsNats) = n2w∘w2n≡id
0-hom +-wordsAsNats = refl

*-wordsAsNats : MonoidEmbedding₂ mulWord mulNat w2n n2w 1 1
Embedding₂.hom   (embedding *-wordsAsNats) = w2n-*-hom
Embedding₂.embed (embedding *-wordsAsNats) = n2w∘w2n≡id
0-hom *-wordsAsNats = refl

addWord-idˡ : Identityˡ addWord 0
addWord-idˡ = map-idˡ addWord addNat w2n n2w 0 0 +-wordsAsNats addNat-idˡ

addWord-idʳ : Identityʳ addWord 0
addWord-idʳ = map-idʳ addWord addNat w2n n2w 0 0 +-wordsAsNats addNat-idʳ

addWord-comm : Commutative addWord
addWord-comm = map-comm addWord addNat w2n n2w (embedding +-wordsAsNats) addNat-comm

addWord-assoc : Associative addWord
addWord-assoc = map-assoc addWord addNat w2n n2w (embedding +-wordsAsNats) addNat-assoc 

mulWord-comm : Commutative mulWord
mulWord-comm = map-comm mulWord mulNat w2n n2w (embedding *-wordsAsNats) mulNat-comm

mulWord-assoc : Associative mulWord
mulWord-assoc = map-assoc mulWord mulNat w2n n2w (embedding *-wordsAsNats) mulNat-assoc

mulWord-idˡ : Identityˡ mulWord 1
mulWord-idˡ = map-idˡ mulWord mulNat w2n n2w 1 1 *-wordsAsNats mulNat-idˡ

mulWord-idʳ : Identityʳ mulWord 1
mulWord-idʳ = map-idʳ mulWord mulNat w2n n2w 1 1 *-wordsAsNats mulNat-idʳ

mulWord-distributeˡ-addWord : Distributiveˡ addWord mulWord
mulWord-distributeˡ-addWord = map-distributeˡ addWord addNat mulWord mulNat w2n n2w n2w∘w2n≡id w2n-+-hom w2n-*-hom mulNat-distributeˡ-addNat

mulWord-distributeʳ-addWord : Distributiveʳ addWord mulWord
mulWord-distributeʳ-addWord = map-distributeʳ addWord addNat mulWord mulNat w2n n2w n2w∘w2n≡id w2n-+-hom w2n-*-hom mulNat-distributeʳ-addNat

-- TODO: I have trouble figuring out negation of words and how
--       to prove the following. Can we prove it?
neg-inv-word : ∀ (x : Word) → addWord x (negateWord x) ≡ 0
neg-inv-word x =
  x + negateWord x                                                ≡⟨⟩
  n2w (w2n x + w2n (negateWord x))                                ≡⟨⟩
  n2w (w2n x + w2n (n2w (monusNat 18446744073709551616 (w2n x)))) ≡⟨ {!!} ⟩
  0 ∎

instance
  open IsLawfulNum

  iLawfulNumWord : IsLawfulNum Word
  +-assoc iLawfulNumWord = addWord-assoc
  +-comm iLawfulNumWord = addWord-comm
  +-idˡ iLawfulNumWord = λ x → addWord-idˡ x
  +-idʳ iLawfulNumWord = λ x → addWord-idʳ x
  neg-inv iLawfulNumWord = λ x → neg-inv-word x
  *-assoc iLawfulNumWord = mulWord-assoc
  *-idˡ iLawfulNumWord = λ x → mulWord-idˡ x
  *-idʳ iLawfulNumWord = λ x → mulWord-idʳ x
  distributeˡ iLawfulNumWord = mulWord-distributeˡ-addWord
  distributeʳ iLawfulNumWord = mulWord-distributeʳ-addWord
