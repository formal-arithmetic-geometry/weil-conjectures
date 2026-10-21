/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DivisorModule
public import WeilConjectures.AlgebraicGeometry.Dimension
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Topology.RingedModuleSkyscraper
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.AlgebraicGeometry.StructureSheaf
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.CoherentFiniteType

/-! # Rational sections and divisor modifications on a regular curve

Source: Stacks Project, Divisors, Tags 0BE8, 0BE9, 02SL, 01WX, 02SF and 0BE6;
the explicit valuation and local quotient calculation of the blueprint
(blueprint: lem-pc-regular-curve-divisor-calculus).

The existing `Divisor.associatedModule` constructs the valuation-bounded subsheaf, using
locally constant rational functions. On a nonempty open of an integral scheme these are
constant; on the empty open they form the zero module. `Scheme.ord` is the normalized
valuation, as specified by the first clause below. The divisor of a rational section is
specified by its coefficients for every local generator, so its finite support and
independence of generators are part of the conclusion rather than assumed data.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- Divisor calculus on an arbitrary integral Noetherian regular scheme of dimension one.
Source: Stacks Project, Divisors, Tags 0BE8, 0BE9, 02SL, 01WX, 02SF, 02SG and 0BE6
(blueprint: lem-pc-regular-curve-divisor-calculus).

`IsNoetherian` includes local Noetherianity and quasi-compactness. Together with `IsRegular`
these are exactly `IsRegularScheme` and the Noetherian hypotheses of the node. No base field,
separatedness or finite-type assumption is made. The zero-divisor identification is expressed
as an isomorphism whose formula identifies the two subsheaves of the rational-function sheaf.
The tensor isomorphism is specified on the image of every presheaf pure tensor. The divisor
of a nonzero generic section is the unique finite divisor with the displayed coefficients;
its isomorphism is multiplication by that section, specified on generic germs. The last
inclusion is the identity on the rational functions representing sections. The residue-field
vector space is restricted to the stalk ring along `X.residue x` before taking its skyscraper.

Proof, following the ten steps in the node:
1. A finite Noetherian affine cover makes the underlying space Noetherian. Sobriety makes it
   T0. The dimension comparison `dim_eq_topologicalKrullDim` shows that every nongeneric point
   is closed: a further specialization would give a chain of length two. The generic point
   is not closed. Every nonempty open contains it and has finite closed complement by
   `IsOpen.finite_compl_of_topologicalKrullDim_le_one`.
2. Embed all stalk rings and sections on nonempty opens into the generic stalk K. In an affine
   chart a closed point is a nonzero prime, so its regular local ring has dimension one and
   is a DVR by `IsRegularLocalRing.isDiscreteValuationRing`. Factor numerator and denominator
   into a unit times a uniformizer power. Two different exponents would put a unit in the
   maximal ideal. Changing the uniformizer by a unit preserves the exponent. This identifies
   `ord` with the normalized valuation, additive on products, with nonnegative values exactly
   on the local ring and value zero exactly on its units.
3. Represent h and its inverse by germs near the generic point. Their product is one by
   injectivity into K. Thus h is a unit on a nonempty open; only finitely many closed points
   outside that open can have nonzero valuation.
4. The valuation lattices are modules. Compatible rational functions on nonempty opens agree
   in K because those opens intersect. They glue with the same bounds. For D=0, membership in
   every local ring gives a regular section by `exists_germToFunctionField_eq`, uniquely.
5. At x choose a uniformizer t and remove the other support points of D and of div(t). The
   bounds identify O(D) there with t^(-D(x)) O. Off the support it is O. These trivializations
   give invertibility, including quasi-coherence after shrinking to affine opens.
6. Multiply rational functions. Additivity of valuations gives a balanced morphism from the
   sheaf tensor product. Locally it sends t^(-D(x)) tensor t^(-E(x)) to t^(-D(x)-E(x)), so it is
   an isomorphism; the inverses glue since they invert the same multiplication morphism.
7. Trivializing at the generic point gives a one-dimensional K-vector space and a nonzero
   section s. At x any two local generators differ by a unit, so their coefficient valuations
   agree. Trivialize near the generic point and restrict to where its coefficient is a unit.
   Orders vanish there; its finite complement proves the coefficient function has finite
   support and hence defines a unique divisor D.
8. In a trivialization s=f e, the bound for g in O(D) is precisely gf regular. The map
   g -> (gf)e and inverse a e -> a/f respect restrictions. They agree on overlaps by equality
   of generic germs, hence glue to the asserted multiplication isomorphism.
9. A nonzero global section has nonzero generic germ, by injectivity in each trivialization.
   Its coefficients belong to the local rings, so all their orders are nonnegative. With
   L=O and s=f this also gives the principal-divisor isomorphism, with the same sign.
10. The natural inclusion O(D-[x]) -> O(D) is the identity on rational sections. At x its
    image is m_x O(D)_x. The quotient V=O(D)_x/m_x O(D)_x is one-dimensional over kappa(x).
    Take germs then this quotient on opens containing x and zero elsewhere. Away from x the
    two divisor modules agree and the skyscraper vanishes. The sequence is therefore short
    exact at every stalk, hence as sheaves by `RingedSpace.module_stalk_exact`. Choosing a
    basis of V gives its noncanonical skyscraper isomorphism with kappa(x). -/
theorem regular_curve_divisor_calculus
    (X : Scheme.{u}) [IsIntegral X] [IsNoetherian X] [IsRegular X] (hdim : X.dim = 1) :
    (∀ x : closedPoints X,
      IsDiscreteValuationRing (X.presheaf.stalk x.val) ∧
      ∀ (f : X.functionFieldˣ) (n : ℤ),
        X.ord (f : X.functionField) x.val = n ↔
          ∃ t : X.presheaf.stalk x.val,
            IsLocalRing.maximalIdeal (X.presheaf.stalk x.val) = Ideal.span {t} ∧
            ∃ a : (X.presheaf.stalk x.val)ˣ,
              (f : X.functionField) =
                algebraMap (X.presheaf.stalk x.val) X.functionField (a : _) *
                  (algebraMap (X.presheaf.stalk x.val) X.functionField t) ^ n) ∧
    (∀ D : X.Divisor, (D.associatedModule X).IsInvertible) ∧
    (∃ e : (0 : X.Divisor).associatedModule X ≅ SheafOfModules.unit X.ringCatSheaf,
      ∀ (U : X.Opens) (hη : genericPoint X ∈ U)
        (a : ((0 : X.Divisor).associatedModule X).val.obj (op U)),
        X.presheaf.germ U (genericPoint X) hη (e.hom.val.app (op U) a) =
          a.val ⟨genericPoint X, hη⟩) ∧
    (∀ D E : X.Divisor,
      ∃ e : D.associatedModule X ⊗ E.associatedModule X ≅ (D + E).associatedModule X,
        ∀ (U : X.Opens) (a : (D.associatedModule X).val.obj (op U))
          (b : (E.associatedModule X).val.obj (op U)) (y : U),
          (e.hom.val.app (op U)
            ((SheafOfModules.tensorObjIsoSheafification (R := X.sheaf)
              (D.associatedModule X) (E.associatedModule X)).inv.val.app (op U)
                (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
                  ((D.associatedModule X).val ⊗ (E.associatedModule X).val)).app (op U)
                    (a ⊗ₜ[Γ(X, U)] b)))).val y = a.val y * b.val y) ∧
    (∀ (L : X.Modules) [L.IsInvertible],
      (∃ s : ↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint X)), s ≠ 0) ∧
      (∀ (s : ↑(TopCat.Presheaf.stalk L.val.presheaf (genericPoint X))), s ≠ 0 →
        ∃! D : X.Divisor,
          (∀ (x : closedPoints X) (e : ↑(TopCat.Presheaf.stalk L.val.presheaf x.val)),
            Submodule.span (X.presheaf.stalk x.val) {e} = ⊤ →
              (∃ f : X.functionFieldˣ,
                s = (f : X.functionField) • TopCat.Presheaf.stalkSpecializes L.val.presheaf
                  ((genericPoint_spec X).specializes (Set.mem_univ x.val)) e) ∧
              (∀ f : X.functionFieldˣ,
                s = (f : X.functionField) • TopCat.Presheaf.stalkSpecializes L.val.presheaf
                  ((genericPoint_spec X).specializes (Set.mem_univ x.val)) e →
                    D x = X.ord (f : X.functionField) x.val)) ∧
          (∃ e : D.associatedModule X ≅ L,
            ∀ (U : X.Opens) (hη : genericPoint X ∈ U)
              (a : (D.associatedModule X).val.obj (op U)),
              TopCat.Presheaf.germ L.val.presheaf U (genericPoint X) hη
                (e.hom.val.app (op U) a) = a.val ⟨genericPoint X, hη⟩ • s) ∧
          (∀ a : L.val.obj (op ⊤),
            TopCat.Presheaf.germ L.val.presheaf ⊤ (genericPoint X) trivial a = s →
              ∀ x : closedPoints X, 0 ≤ D x)) ∧
      (∀ a : L.val.obj (op ⊤), a ≠ 0 →
        TopCat.Presheaf.germ L.val.presheaf ⊤ (genericPoint X) trivial a ≠ 0)) ∧
    (∀ f : X.functionFieldˣ,
      ∃ e : (X.div (Additive.ofMul f)).associatedModule X ≅
          SheafOfModules.unit X.ringCatSheaf,
        ∀ (U : X.Opens) (hη : genericPoint X ∈ U)
          (a : ((X.div (Additive.ofMul f)).associatedModule X).val.obj (op U)),
          X.presheaf.germ U (genericPoint X) hη (e.hom.val.app (op U) a) =
            a.val ⟨genericPoint X, hη⟩ * (f : X.functionField)) ∧
    (∀ (D : X.Divisor) (x : closedPoints X),
      ∃ V : ModuleCat.{u} (X.residueField x.val),
        Module.finrank (X.residueField x.val) V = 1 ∧
        ∃ (i : (D - Finsupp.single x 1).associatedModule X ⟶ D.associatedModule X)
          (q : D.associatedModule X ⟶
            SheafOfModules.ringedModuleSkyscraper X.toRingedSpace x.val
              ((ModuleCat.restrictScalars (X.residue x.val).hom).obj V)),
          (∀ (U : X.Opens)
            (a : ((D - Finsupp.single x 1).associatedModule X).val.obj (op U)) (y : U),
              (i.val.app (op U) a).val y = a.val y) ∧
          (∃ w : i ≫ q = 0, (ShortComplex.mk i q w).ShortExact) ∧
          Nonempty (SheafOfModules.ringedModuleSkyscraper X.toRingedSpace x.val
              ((ModuleCat.restrictScalars (X.residue x.val).hom).obj V) ≅
            SheafOfModules.ringedModuleSkyscraper X.toRingedSpace x.val
              ((ModuleCat.restrictScalars (X.residue x.val).hom).obj
                (ModuleCat.of (X.residueField x.val) (X.residueField x.val))))) := by
  sorry

end AlgebraicGeometry.Scheme
