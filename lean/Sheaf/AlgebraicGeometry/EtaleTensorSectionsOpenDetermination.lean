/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q148
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorOpenSectionsNaturality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Sheaf.AlgebraicGeometry.EtaleTensorSectionsLocalSpan
import Mathlib.Algebra.Category.Grp.ForgetCorepresentable

/-!
# Maps from tensor sections are determined on opens

Source: Stacks Project, Descent, Tag 070S, omitted proof of (2)
(blueprint: lem-trf-etale-tensor-sections-open-determination).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction to open subschemes is injective on module-presheaf maps from the
specified tensor-sections presheaf. The target sheaf is unpacked as a module presheaf
`G` with its sheaf condition `hG`; its ring presheaf is exactly regular functions on
etale objects. The two morphisms are unpacked as families of linear maps with their
naturality equations. This permits an independent universe for the target modules.
The inverse of `tensorOpenSectionIso` is the global-section map of the canonical,
unit-compatible restriction-to-tensor-pullback comparison, including the canonical
identification of sections on an open subscheme with sections on the corresponding open.

Source: Stacks Project, Descent, Tag 070S, lemma-compare-sites, omitted proof of (2)
(blueprint: lem-trf-etale-tensor-sections-open-determination).

Proof, following the six steps of the DAG:
1. For an etale u : V to T restrict G to the open subschemes of V. Open covers
   are etale covers, so hG makes this a Zariski module sheaf G_u.
2. Put N = u^*M. On every open A of V, compose the unit-compatible comparison
   N(A) to Gamma(A,j_A^*N) with the normalized pullback-composition comparison,
   obtaining an isomorphism e_A : N(A) to P_M(u j_A). Naturality of the open-section
   comparison and associativity of normalized composition give compatibility with
   restrictions. These are new-etale-tensor-open-section-iso, its naturality node,
   and lem-sc-left-adjoint-composition-iso-associativity.
3. For either family xi, compose xi at u j_A with e_A. The naturality hypothesis
   makes these a morphism a^xi : u^*M to G_u of Zariski modules.
4. For W open in T and A its inverse image in V, factor u j_A through W via v.
   Both e_A applied to the u-unit of m and the restriction along v of the canonical
   open pullback of m equal the unit for u j_A. This follows from the unit equations
   of lem-weil-pbc-open-immersion-module-pullback-restriction and
   lem-sc-etale-qcoherent-presheaf-functorial.
5. By lem-pc-module-pullback-adjunction, the adjunct of a^xi on W sends m to
   G(v) applied to xi at W applied to the canonical open pullback of m. The hypothesis
   h_open equates these adjuncts. Injectivity of the adjunction equates the a^xi.
6. Evaluate this equality at the whole open V and cancel e_V, using the canonical
   whole-open isomorphism and naturality. The components agree at every etale object;
   hence the morphisms agree, including their naturality on all arrows. Empty schemes,
   empty opens and the zero module are included. No quasi-coherence is used. -/
theorem etaleTensorSections_open_determination (T : Scheme.{u}) (M : T.Modules)
    (G : _root_.PresheafOfModules.{v}
      ((Scheme.Etale.forget T ⋙ Over.forget T).op ⋙ Scheme.Γ ⋙
        forget₂ CommRingCat.{u} RingCat.{u}))
    (hG : Presheaf.IsSheaf T.smallEtaleTopology G.presheaf)
    (θ θ' : ∀ V : T.Etale,
      Γ((tensorPullback V.hom).obj M, ⊤) →ₗ[Γ(V.left, ⊤)] G.obj (op V))
    (hθ : ∀ (U V : T.Etale) (g : V ⟶ U)
      (s : Γ((tensorPullback U.hom).obj M, ⊤)),
      θ V (etaleTensorSectionsRestriction M g s) = G.map g.op (θ U s))
    (hθ' : ∀ (U V : T.Etale) (g : V ⟶ U)
      (s : Γ((tensorPullback U.hom).obj M, ⊤)),
      θ' V (etaleTensorSectionsRestriction M g s) = G.map g.op (θ' U s))
    (h_open : ∀ (W : T.Opens) (m : Γ(M, W)),
      θ (Scheme.Etale.mk W.ι) ((tensorOpenSectionIso T M W).inv m) =
        θ' (Scheme.Etale.mk W.ι) ((tensorOpenSectionIso T M W).inv m)) :
    θ = θ' := by
  -- Local generation gives a sectionwise version of the adjunction argument above.
  have hgen (U : T.Etale) : Set.EqOn (θ U) (θ' U)
      {t | ∃ (W : T.Opens) (m : Γ(M, W)) (f : U ⟶ Scheme.Etale.mk W.ι),
        etaleTensorSectionsRestriction M f ((tensorOpenSectionIso T M W).inv m) = t} := by
    rintro _ ⟨W, m, f, rfl⟩
    rw [hθ, hθ', h_open]
  funext V
  apply LinearMap.ext
  intro s
  obtain ⟨S, hS, hs⟩ := etaleTensorSections_locally_span_open T M V s
  have htypes : Presieve.IsSheaf T.smallEtaleTopology
      (G.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) :=
    Presieve.isSheaf_iso _
      (Functor.isoWhiskerLeft G.presheaf AddCommGrpCat.coyonedaObjIsoForget) (hG _)
  apply (htypes S hS).isSeparatedFor.ext
  intro U g hg
  change G.map g.op (θ V s) = G.map g.op (θ' V s)
  rw [← hθ, ← hθ']
  exact LinearMap.eqOn_span (hgen U) (hs U g hg)

end AlgebraicGeometry.Scheme.Modules
