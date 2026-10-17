/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NR
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Sheaf.CategoryTheory.Sites.CohomologyOverObjectLocalization
import Sheaf.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.AbelianEtaleProEtaleCohomologyComparison
import Sheaf.AlgebraicGeometry.AffineSepclosedEtaleAcyclic
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.RingTheory.WeaklyEtaleField
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence

/-!
# Affine sections of functions modulo the constant pro-etale sheaf

Source: Stacks Project, Tag 0F6D, Example `example-functions-mod-locally-constant-functions`
(blueprint: lem-cbc-proetale-functions-quotient-sections).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Tag 0F6D
(blueprint: lem-cbc-proetale-functions-quotient-sections).
The functions presheaf is represented here by a sheaf `F`, with additive section
identifications `e` compatible with precomposition. The morphism `i` sends constant
sections to constant functions and its image is exactly the locally constant functions.
The first cokernel comparison identifies sheafification of the presheaf cokernel with
the sheaf cokernel, compatibly with their projections. The affine comparison sends a
function class to its image under the sheaf cokernel projection, specifying canonicity.

Proof plan:
1. Apply lem-cbc-continuous-functions-fpqc-sheaf with the indiscrete topology to obtain
all functions, and with the discrete topology to obtain locally constant functions.
Restrict these fpqc sheaves to the pro-etale site.
2. Glue constant values along open covers to identify locally constant functions with
constantSheaf (def-weil-pbc-constant-sheaf, def-weil-pbc-sheafification). Inclusion of
functions is componentwise injective, hence a monomorphism.
3. Sheafification preserves cokernels (lem-weil-pbc-sheafification-exact), giving the
short exact sequence with the abelian-sheaf cokernel.
4. For a weakly etale object over the stated base, closedness and separable closedness
pass to its points: use weakly etale base change, the weakly etale field description,
and lem-pc-sepclosed-finite-sep-trivial. The fibre over a closed base point is closed;
its affine coordinate rings are integral over a field and have separable residue fields.
5. The etale/pro-etale comparison identifies H1 of the constant sheaf with etale H1,
which vanishes by lem-cbc-affine-sepclosed-etale-acyclic. Slice localization identifies
this with object cohomology (lem-weil-pbc-proetale-restriction-injectives and
lem-weil-pbc-cohomology-over-object-localization).
6. Apply lem-weil-pbc-derived-functor-long-exact. The vanishing makes the cokernel
projection surjective on affine sections, with kernel the locally constant functions.
The first isomorphism theorem gives the displayed additive equivalence. -/
theorem exists_proEtale_functions_quotient_sections (X : Scheme.{u})
    (A : Type (u + 1)) [AddCommGroup A] :
    ∃ (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1})
      (e : ∀ V : X.ProEt, F.obj.obj (op V) ≃+ (V.left → A)),
      (∀ (U V : X.ProEt) (f : U ⟶ V) (s : F.obj.obj (op V)) (x : U.left),
        e U (F.obj.map f.op s) x = e V s (f.left x)) ∧
      ∃ (i : (constantSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of A) ⟶ F),
        Mono i ∧
        (∀ (V : X.ProEt) (a : A) (x : V.left),
          e V (i.hom.app (op V)
            ((toSheafify (ProEt.topology X)
              ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of A))).app (op V) a)) x = a) ∧
        (∀ (V : X.ProEt) (f : V.left → A),
          (∃ s, e V (i.hom.app (op V) s) = f) ↔ IsLocallyConstant f) ∧
        (∃ c : (presheafToSheaf (ProEt.topology X) AddCommGrpCat.{u + 1}).obj
            (cokernel i.hom) ≅ cokernel i,
          ∀ (V : X.ProEt) (s : F.obj.obj (op V)),
            c.hom.hom.app (op V)
                ((toSheafify (ProEt.topology X) (cokernel i.hom)).app (op V)
                  ((cokernel.π i.hom).app (op V) s)) =
              (cokernel.π i).hom.app (op V) s) ∧
        ((∀ x : X, IsClosed ({x} : Set X)) →
          (∀ x : X, IsSepClosed (X.residueField x)) →
          ∀ (V : X.ProEt), IsAffine V.left →
            ∃ q : ((V.left → A) ⧸
                (LocallyConstant.coeFnAddMonoidHom : LocallyConstant V.left A →+
                  (V.left → A)).range) ≃+ (cokernel i).obj.obj (op V),
              ∀ f : V.left → A,
                q (QuotientAddGroup.mk f) =
                  (cokernel.π i).hom.app (op V) ((e V).symm f)) := by
  sorry

end AlgebraicGeometry.Scheme
