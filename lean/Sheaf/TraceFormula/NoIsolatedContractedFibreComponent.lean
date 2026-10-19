module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Sheaf.AlgebraicGeometry.SchemeUniverseEnlargement
import WeilConjectures.RingTheory.Flat.LocalizationPreservesFlatness
import WeilConjectures.AlgebraicGeometry.ConstantLocalDimensionComponents
import WeilConjectures.AlgebraicGeometry.EquidimensionalOpenLocalDimension
import WeilConjectures.AlgebraicGeometry.NoetherianSpecializationTrait
import Sheaf.TraceFormula.FlatDenseGenericFibrePureDimension
import WeilConjectures.FieldTheory.CommonExtensionFields
import WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import Sheaf.AlgebraicGeometry.SteinFactorizationAffine
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-!
# A curve modification cannot contract an isolated whole fibre component

Source: Temkin, Stable modification, proof of Theorem 1.1, p. 3; the
non-isolated contracted-subcurve input in the stable pointed-subcurve argument
(blueprint: lem-trf-no-isolated-contracted-fibre-component).
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/--
Source: Temkin, Stable modification, proof of Theorem 1.1, p. 3; auxiliary
noncontraction statement for a proper modification of relative curves
(blueprint: lem-trf-no-isolated-contracted-fibre-component).

Proof route (the proof is postponed in this stage):
Step 1: Suppose that a component W as in the statement is mapped to a point x, and write s for
the image of Spec Omega in T. The geometric fibre Y_Omega is Noetherian by finite-type base
change and the finite-type-over-Noetherian lemma. Its finitely many irreducible components cover
it. Group these components by chains of nonempty intersections: the union in each group is
connected and closed, and its complement is the union of the other finitely many groups, hence
closed. These groups are exactly the connected components. Consequently W is an open-and-closed
subscheme. It has a closed point w by quasi-compactness and the Kolmogorov property of a scheme.
Since W is of finite type over the algebraically closed field Omega, kappa(w)=Omega; its image
gives an Omega-rational point x of X_Omega. If s=eta, f_Omega is an isomorphism and W contains
an entire one-dimensional irreducible component, so its image cannot be a point. Hence s is
distinct from eta.

Step 2: Apply the Noetherian specialization-trait lemma to eta specializing to s in T. It
supplies a DVR R and a:Spec R -> T with closed point r mapping to s and generic point mapping to
eta. Put K=Frac(R), X_R=X times_T Spec R, Y_R=Y times_T Spec R, and f_R=f times_T Spec R. The
map on generic fibres is an isomorphism. The definition of a DVR makes R a Noetherian local PID,
a valuation ring, and a domain; fix a nonzero uniformizer pi.

Step 3: Choose a common extension M of Omega and kappa(r) over kappa(s), then an algebraic
closure L of M. Thus the closed geometric fibre of Y_R over L identifies with Y_L=Y_Omega
times_Omega L. Let W_L be the inverse image of W; it is open and closed. It is nonempty: a point
of W with residue field E lifts after choosing a common extension of E and L over Omega. Its
image under f_L is the single L-rational point x_L. Here this assertion does not presume
schematic constancy or reducedness: in an affine neighbourhood of x, every function in the
maximal ideal of x pulls back on each affine of W to a nilpotent (it belongs to every prime).
After scalar extension these functions are still nilpotent, so the image is contained in the
base change of the rational point x; that base change has one point. Nonemptiness gives
equality.

Step 4: The morphisms X_R -> Spec R and Y_R -> Spec R are of finite type by finite-type base
change. They are flat: on an affine base-change chart, if C is flat over A, then C tensor_A R is
flat over R, since for an injection N1 -> N2 of R-modules, Ni tensor_R (R tensor_A C) identifies
with Ni tensor_A C and the latter injection follows from flatness of C. Apply the affine
criterion, including localization on the charts. Restriction to an open preserves the same
criterion. This verifies flatness without any regularity, excellence, or separatedness
assumption on T.

Step 5: Let x0 be the image of x_L in X_R. Choose an affine open U=Spec A of X_R containing x0
and put V=f_R^{-1}(U). The entire W_L lies in V_L. Properness is preserved first under the base
change T <- Spec R and then under the open base change U -> X_R, so V -> U is proper. Since X_R
is of finite type over the Noetherian affine Spec R, X_R is Noetherian; its affine open U is
Noetherian and of finite type over R (all its opens are quasi-compact). The proper finite-type
scheme V over U is Noetherian. In particular V is quasi-compact and quasi-separated as a scheme:
every intersection of affine opens is an open subset of its Noetherian underlying space and is
therefore quasi-compact.

Step 6: Put B=Gamma(V,O_V) and take the affine Stein factorization V --q--> Z=Spec B --h--> U.
The affine Stein theorem says that q is proper with geometrically connected, nonempty fibres.
Since V is locally Noetherian, O_V is coherent: it is quasi-coherent of finite type. Proper
coherent cohomology over the Noetherian ring A, in degree zero, now says that B is a finite
A-module. Thus h is finite by the definition of a finite morphism. In particular B is a
finite-type R-algebra and Z is Noetherian. This use of coherent cohomology is over U, not over
Spec R; V need not be proper over Spec R.

Step 7: The R-module B is torsion free. Indeed, for any affine chart V_i=Spec C_i of V, flatness
of V/R and the affine criterion make C_i flat over R. For 0 != b in R, tensor the injection R
--b--> R with C_i: multiplication by b on C_i is injective. If b z=0 for a global section z in
B, its restriction to every V_i is therefore zero, hence z=0 by the sheaf condition. Since R is
a valuation ring, the torsion-free-module-flat lemma of this unit applies to B. The affine
criterion gives flatness of Z -> Spec R.

Step 8: Because V is quasi-compact and quasi-separated, flat base change of global sections
along Spec K -> Spec R gives B tensor_R K = Gamma(V_K,O). The localization R -> K is flat: apply
the localization-preserves-flatness lemma to the free rank-one R-module R. The generic
isomorphism f_K identifies V_K with U_K, which is affine (U_K=Spec(A tensor_R K)). Therefore
h_K:Z_K -> U_K is an isomorphism, with the canonical ring identification above. No assertion of
global-sections base change along the nonflat closed-fibre map R -> L is used.

Step 9: The generic fibre Z_K is pure of dimension one. To check this precisely over K, take an
algebraic closure Kbar. The scheme X_Kbar is a geometric fibre of X/T, hence every irreducible
component has dimension one. Its local topological dimension is one everywhere by the
equidimensional-open lemma with O=X_Kbar. Each point of X_K lifts after field extension (the
common-extension-fields argument applied to its residue field). On affine charts, invariance of
local topological dimension under field extension therefore gives dimension one at every point
of X_K. Local topological dimension is unchanged on an open neighbourhood, directly from its
definition. Thus it is one throughout U_K. The constant-local-dimension-components lemma,
applied to this locally Noetherian open, makes U_K pure one-dimensional. Transfer this along the
isomorphism Z_K=U_K from Step 8.

Step 10: The generic fibre Z_K=D(pi) is dense in Z. Indeed, if a basic open D(b) is disjoint
from D(pi), then b pi belongs to every prime, so (b pi)^n=0 for some n. Torsion-freeness of B
over the domain R implies b^n=0, hence D(b) is empty. Now apply the flat-dense-generic-fibre
pure-dimension lemma to Z -> Spec R, with d=1. Its base is integral, it is flat by Step 7 and
locally of finite type by Step 6, and Steps 9 and this paragraph verify its generic-fibre
hypotheses. In particular the geometric closed fibre Z_L is pure one-dimensional.

Step 11: Base change q to L. Its fibres remain connected and nonempty, and q_L is proper and
hence closed. A connected fibre meets at most one of the disjoint clopen subsets W_L and V_L
minus W_L. Consequently F=q_L(W_L) satisfies q_L^{-1}(F)=W_L. Surjectivity implies q_L(V_L minus
W_L)=Z_L minus F. Both images are closed, so F is a nonempty clopen subset of Z_L. Since h_L
q_L=f_L, we have h_L(F)={x_L}. The finite morphism h remains finite after this affine base
change: if B is generated by b1,...,bn as an A-module, their tensors generate B tensor_R L as an
A tensor_R L-module. Thus its fibre over x_L is finite.

Step 12: Every point in h_L^{-1}(x_L) is closed in Z_L. In fact x_L is an L-rational point in
the affine U_L, hence is closed there, and its inverse image is the spectrum of a
finite-dimensional L-algebra. The quotient by any prime is a finite-dimensional L-domain, hence
a field by the cited lemma; its primes are therefore maximal. Thus the finite subset F is a
finite discrete closed subset. Since F is also open in Z_L, each of its singleton subsets is
open in Z_L and has local topological dimension zero. But Z_L is locally of finite type over L
and pure one-dimensional by Step 10, so the equidimensional-open-local-dimension lemma says that
its local topological dimension is one at every point. This contradicts F being nonempty.

Step 13: This contradiction excludes the assumed W. Finally, an irreducible component C of
Y_Omega disjoint from every other irreducible component is closed, and its complement is the
finite union of those other closed components. Hence C is open as well. It is nonempty and
irreducible, therefore connected, and no connected subset can meet both C and its clopen
complement. It is a connected component. If C is proper, the assertion just proved excludes its
contraction. This proves both conclusions with the original hypotheses; smoothness, nodality,
schematic density, and properness of W were not needed beyond the finite-type hypotheses used
above.
-/
theorem no_isolated_contracted_fibre_component
    {T X Y : Scheme.{u}}
    [IsIntegral T] [IsNoetherian T]
    (η : T) (hη : IsGenericPoint η (Set.univ : Set T))
    (pX : X ⟶ T) (pY : Y ⟶ T)
    [Flat pX] [LocallyOfFinitePresentation pX] [QuasiCompact pX]
    [QuasiSeparated pX]
    [Flat pY] [LocallyOfFinitePresentation pY] [QuasiCompact pY]
    [QuasiSeparated pY]
    (hXdim : ∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ schemeUniverseLift.{u, v} T),
      (∀ Z : Set (↥(pullback (schemeUniverseLiftMap.{u, v} pX) s)),
        Z ∈ irreducibleComponents (↥(pullback (schemeUniverseLiftMap.{u, v} pX) s)) →
          topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    (hYdim : ∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ schemeUniverseLift.{u, v} T),
      (∀ Z : Set (↥(pullback (schemeUniverseLiftMap.{u, v} pY) s)),
        Z ∈ irreducibleComponents (↥(pullback (schemeUniverseLiftMap.{u, v} pY) s)) →
          topologicalKrullDim Z = (1 : WithBot ℕ∞)))
    [Smooth (pX.fiberToSpecResidueField η)]
    (hYnode : ∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ schemeUniverseLift.{u, v} T)
      (x : ↥(pullback (schemeUniverseLiftMap.{u, v} pY) s)),
      (¬ ∃ U : (pullback (schemeUniverseLiftMap.{u, v} pY) s).Opens,
        x ∈ U ∧ Smooth (U.ι ≫ pullback.snd (schemeUniverseLiftMap.{u, v} pY) s)) →
      Nonempty
        (AdicCompletion (IsLocalRing.maximalIdeal
          ((pullback (schemeUniverseLiftMap.{u, v} pY) s).presheaf.stalk x))
          ((pullback (schemeUniverseLiftMap.{u, v} pY) s).presheaf.stalk x) ≃+*
            (MvPowerSeries (Fin 2) Ω ⧸
              Ideal.span ({(MvPowerSeries.X (0 : Fin 2) *
                MvPowerSeries.X (1 : Fin 2))} : Set (MvPowerSeries (Fin 2) Ω)))))
    (g : Y ⟶ X) (hg : g ≫ pX = pY)
    [IsProper g]
    [IsIso (pullback.map pY (T.fromSpecResidueField η)
      pX (T.fromSpecResidueField η) g (𝟙 _) (𝟙 T)
      (by simpa using hg.symm) (by simp))]
    (hdense : ∃ U : X.Opens,
      (∀ W : X.Opens, Function.Injective (U.ι.app W)) ∧
      (∀ W : Y.Opens,
        Function.Injective ((g ⁻¹ᵁ U).ι.app W)) ∧
      IsIso (pullback.snd g U.ι)) :
    (∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ schemeUniverseLift.{u, v} T)
      (x : ↥(pullback (schemeUniverseLiftMap.{u, v} pY) s))
      (W : Scheme.{max u v}) (i : W ⟶ pullback (schemeUniverseLiftMap.{u, v} pY) s),
      IsOpenImmersion i → IsClosedImmersion i →
      Set.range i = connectedComponent x →
      _root_.IsConnected (Set.range i) →
      IsProper (i ≫ pullback.snd (schemeUniverseLiftMap.{u, v} pY) s) →
      ¬ (Set.range
        (i ≫ pullback.map (schemeUniverseLiftMap.{u, v} pY) s
          (schemeUniverseLiftMap.{u, v} pX) s (schemeUniverseLiftMap.{u, v} g) (𝟙 _) (𝟙 _)
          (by simp only [Category.comp_id]
              rw [← schemeUniverseLiftMap_comp, hg]) (by simp))).Subsingleton) ∧
    (∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (.of Ω) ⟶ schemeUniverseLift.{u, v} T)
      (C : Scheme.{max u v}) (i : C ⟶ pullback (schemeUniverseLiftMap.{u, v} pY) s),
      IsClosedImmersion i →
      Set.range i ∈ irreducibleComponents (↥(pullback (schemeUniverseLiftMap.{u, v} pY) s)) →
      (∀ D : Set (↥(pullback (schemeUniverseLiftMap.{u, v} pY) s)),
        D ∈ irreducibleComponents (↥(pullback (schemeUniverseLiftMap.{u, v} pY) s)) →
        D ≠ Set.range i → Disjoint D (Set.range i)) →
      IsProper (i ≫ pullback.snd (schemeUniverseLiftMap.{u, v} pY) s) →
      ¬ (Set.range
        (i ≫ pullback.map (schemeUniverseLiftMap.{u, v} pY) s
          (schemeUniverseLiftMap.{u, v} pX) s (schemeUniverseLiftMap.{u, v} g) (𝟙 _) (𝟙 _)
          (by simp only [Category.comp_id]
              rw [← schemeUniverseLiftMap_comp, hg]) (by simp))).Subsingleton) := by
  sorry

end AlgebraicGeometry
