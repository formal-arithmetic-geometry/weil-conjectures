module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.ULift
public import Sheaf.CategoryTheory.CompactObject
import Sheaf.CategoryTheory.DerivedModuleDirectSums

@[expose] public section

universe w vH
namespace CategoryTheory
open Limits DirectSum

open Classical in
/-- Surjectivity of the rank-one comparison map.

Proof in words: evaluation at the lifted unit identifies linear maps from ULift S with
vectors, and makes this module free of rank one, hence projective. Its degree-zero complex
is K-projective: a chain map into an acyclic complex is specified by a zero-cycle, which has
a preimage under the preceding differential, giving a null homotopy. Localization on maps
out of this complex thus identifies derived maps naturally and additively with H^0.
Choose complexes representing E i. By derivedModuleDirectSums their termwise coproduct,
with the canonical inclusions, represents the categorical coproduct. Every zero-cycle in
this termwise sum has finite support, and each coordinate is a zero-cycle. A given derived
map from P to the coproduct therefore has a zero-cycle representative with finite support.
Each coordinate determines a derived map P to E i under the preceding identification.
Put these maps into the algebraic direct sum. Naturality of the identification with H^0
shows that their image under the canonical comparison is the given map. This proves
surjectivity. The empty sum has zero H^0, so its only map has the zero preimage; for the zero
ring all modules are zero. No commutativity is used. Source: Stacks Project, Tag 0F5X,
first paragraph. (blueprint: new-stage3-derived-module-rank-one-compact-surjective)
-/
theorem derivedModule_rankOne_comparison_surjective
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))]
    (I : Type (max w vH))
    (E : I → DerivedCategory (ModuleCat.{max w vH} S)) :
    let _ := Classical.decEq I
    let P := (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
      (ModuleCat.of S (ULift.{vH} S))
    Function.Surjective
      (DirectSum.toAddMonoid (fun i : I => Preadditive.rightComp P (Sigma.ι E i)) :
        (⨁ i : I, (P ⟶ E i)) →+ (P ⟶ ∐ E)) := by sorry

end CategoryTheory
