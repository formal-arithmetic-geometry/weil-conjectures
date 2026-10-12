module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

import Sheaf.AlgebraicGeometry.ArtinSchreierPolynomialCover
import Sheaf.AlgebraicGeometry.ArtinSchreierSectionKernel

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

set_option autoImplicit false

/-- Exactness for specified Artin--Schreier maps, assuming their section formulas.
Source: Stacks Project, Tag 0A3J, opening sequence, and Tag 03PL, polynomial cover.
(blueprint: lem-sc-artin-schreier-scheme-section-exact).

Proof: Use a and hrestr to identify G with the additive sheaf of functions. The
hypothesis hp pulls back to every étale U. For any function f on U, cover U by
its affine opens Spec A. On each open, B = A[T]/(T^p - T - f) is finite free of
rank p > 0 and faithfully flat. Its derivative is -1, so Spec B → Spec A is
étale and surjective. Composing with the affine opens gives a covering of U.
The class of T is a preimage of f by hwp, so wp is locally surjective and epi.
On a geometric stalk the same formulas identify wp with x ↦ x^p - x in the
strict local ring and iota with the canonical prime-field map. The local-ring
Artin--Schreier kernel theorem says that every root has a unique prime-field
value. The constant sheaf stalk is ZMod p; its map is injective because the
strict local ring is nonzero. Thus iota is injective on all geometric stalks
and its image is the kernel of wp. Exactness and conservativity of geometric
stalks give Mono iota and exactness of the short complex. Together with Epi wp,
ShortExact.mk' gives the conclusion. If X is empty, every sheaf of abelian
groups on its étale site is zero, and the same conclusion holds; the stalkwise
criterion has an empty family of points. This proof constructs no new maps.
-/
theorem artinSchreier_section_data_shortExact (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hp : (p : Γ(X, ⊤)) = 0)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : ∀ U : X.Etaleᵒᵖ, G.obj.obj U ≃+ Γ(U.unop.left, ⊤))
    (wp : G ⟶ G) (iota : X.constantZMod p ⟶ G) (hzero : iota ≫ wp = 0)
    (hrestr : ∀ (U V : X.Etaleᵒᵖ) (g : U ⟶ V) (x : G.obj.obj U),
      a V (G.obj.map g x) = g.unop.left.appTop (a U x))
    (hwp : ∀ (U : X.Etaleᵒᵖ) (x : G.obj.obj U),
      a U (wp.hom.app U x) = (a U x) ^ p - a U x)
    (hiota : ∀ (U : X.Etaleᵒᵖ) (c : ZMod p),
      a U (iota.hom.app U
        ((toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))))).app U (ULift.up c))) =
        (c.val : Γ(U.unop.left, ⊤))) :
    (ShortComplex.mk iota wp hzero).ShortExact := by
  have hlocal : Sheaf.IsLocallySurjective wp := by
    constructor
    intro U s
    have hpU : (p : Γ(U.left, ⊤)) = 0 := by
      have h := congrArg U.hom.appTop hp
      simpa only [map_natCast, map_zero] using h
    obtain ⟨V, f, hf, hsurj, ω, hω⟩ :=
      exists_etale_surjective_artinSchreier_eq_appTop p (Fact.out : p.Prime) hpU
        (a (Opposite.op U) s)
    have : Etale (f ≫ U.hom) := by have := U.prop; infer_instance
    let W : X.Etale := Etale.mk (f ≫ U.hom)
    let g : W ⟶ U := MorphismProperty.Over.homMk f rfl
    refine GrothendieckTopology.superset_covering _ ?_
      ((ofArrows_mem_smallEtaleTopology_iff (fun _ : Unit ↦ g)).2 ?_)
    · rw [Sieve.ofArrows, Sieve.generate_le_iff]
      rintro _ _ ⟨⟩
      refine ⟨(a (Opposite.op W)).symm ω, ?_⟩
      apply (a (Opposite.op W)).injective
      rw [hwp, AddEquiv.apply_symm_apply, hrestr]
      exact hω
    · simp only [Set.iUnion_const]
      exact Set.range_eq_univ.mpr hsurj.surj
  have : Epi wp := by infer_instance
  obtain ⟨hk⟩ :=
    artinSchreier_section_data_isKernel X p hp G a wp iota hzero hrestr hwp hiota
  have : Mono iota := Limits.mono_of_isLimit_fork hk
  exact ShortComplex.ShortExact.mk
    ((ShortComplex.mk iota wp hzero).exact_of_f_is_kernel hk)

end AlgebraicGeometry.Scheme
