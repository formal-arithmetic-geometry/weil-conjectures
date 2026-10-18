module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Open immersions of algebraic spaces are etale-local on the target

Source: Stacks Project, Spaces and Morphisms, Tag 03M4, and Spaces Descent,
Tag 041X (blueprint: lem-trf-space-open-immersion-etale-local).
This stage-2 delivery records the statement with its proof intentionally postponed.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Open immersions of algebraic spaces descend along a jointly surjective etale
family of scheme maps. The proof is the compatible-open descent and fppf sheaf
argument of Tags 03M4 and 041X, using the open-subscheme fpqc descent lemma
(lem-weil-pbc-open-subscheme-fpqc-descent), the etale-to-fpqc comparison
(lem-weil-pbc-fpqc-finer-than-etale), and base change of open immersions
(lem-weil-pbc-open-immersion-base-change).
(blueprint: lem-trf-space-open-immersion-etale-local) -/
theorem isOpenImmersion_of_etale_cover
    {S : Scheme.{u}} {X P : AlgebraicSpace S} (a : X ⟶ P)
    (I : Type u) (P_i : I → Over S)
    (p_i : ∀ i, yoneda.obj (P_i i) ⟶ P.obj.obj)
    (h_etale : ∀ i, IsEtale (p_i i))
    (h_joint : ∀ (T : Over S) (x : P.obj.obj.obj (Opposite.op T)),
      ∃ (R : Sieve T.left), R ∈ Scheme.fppfTopology T.left ∧
        ∀ (U : Over S) (f : U ⟶ T), R f.left →
          ∃ (i : I) (y : (yoneda.obj (P_i i)).obj (Opposite.op U)),
            (p_i i).app (Opposite.op U) y = P.obj.obj.map f.op x)
    (h_open : ∀ i,
      AlgebraicSpace.IsRepresentableWith
        (fun _ _ q => IsOpenImmersion q.left)
        (pullback.snd a.hom.hom (p_i i))) :
    AlgebraicSpace.IsRepresentableWith
      (fun _ _ q => IsOpenImmersion q.left) a.hom.hom := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
