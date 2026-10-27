/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q76
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import WeilConjectures.AlgebraicGeometry.FunctionField
public import WeilConjectures.AlgebraicGeometry.StalkAut
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import Sheaf.AlgebraicGeometry.PureDimension
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Fixed
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Localization.Integral
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleFibreDiscreteSeparablePoints
import WeilConjectures.AlgebraicGeometry.EtaleCoproductOfFiniteSeparableFields
import Sheaf.FieldTheory.MultiradicalGaloisDegree
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.AlgebraicGeometry.FiniteDominantNormalUniversallyOpen

/-! # The orbit Kummer field and its normal relative model

Source: de Jong, Families of curves and alterations (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model)

The helper declarations only name the displayed fields, generic maps, reduced orbit union,
and fibre-product lifting set. All use actual relative normalizations and field adjunctions.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The generic curve of the given family, with its chosen pullback model.
Source: de Jong (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model) -/
noncomputable abbrev orbitKummerGenericCurve {X S : Scheme.{u}} [IsIntegral S] (f : X ⟶ S) :
    Scheme.{u} :=
  pullback f S.fromSpecFunctionField

/-- The generic point of the generic curve, using the specified canonical field embedding.
Source: de Jong (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model) -/
noncomputable def orbitKummerGenericPoint {X S : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (f : X ⟶ S) [Algebra S.functionField X.functionField]
    (hKF : X.fromSpecFunctionField ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField X.functionField)) ≫
        S.fromSpecFunctionField) :
    Spec X.functionField ⟶ orbitKummerGenericCurve f :=
  pullback.lift X.fromSpecFunctionField
    (Spec.map (CommRingCat.ofHom (algebraMap S.functionField X.functionField))) hKF

/-- The finite orbit list of radicands, with the second index distinguishing x and x - 1.
Source: de Jong (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model) -/
def orbitKummerRadicand (G : Type v) [Group G] (F : Type u) [Field F]
    [MulSemiringAction G F] {m : ℕ} (x : Fin m → F) (i : Fin m) (g : G) (b : Bool) : F :=
  g • (if b then x i else x i - 1)

/-- The radical field inside the specified algebraic closure. Adjoining all roots is independent
of root choices; in the presence of the given primitive root it is the displayed radical field.
Source: de Jong (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model) -/
noncomputable def orbitKummerField (G : Type v) [Group G] (F Ω : Type u)
    [Field F] [Field Ω] [Algebra F Ω] [MulSemiringAction G F]
    {m : ℕ} (x : Fin m → F) (ell : ℕ) : IntermediateField F Ω :=
  IntermediateField.adjoin F {z : Ω | ∃ (i : Fin m) (g : G) (b : Bool),
    z ^ ell = algebraMap F Ω (orbitKummerRadicand G F x i g b)}

/-- The reduced closed orbit union of the three inverse images. The theorem identifies its
underlying set with the union itself, so taking closure introduces no extra point.
Source: de Jong (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model) -/
def orbitKummerBranchLocus {C : Scheme.{u}} {K : Type u} [Field K]
    (G : Type v) [Group G] (σC : G →* Aut C) {m : ℕ}
    (ψ : Fin m → (C ⟶ ProjectiveLine (Spec (.of K)))) : Closeds C :=
  Closeds.closure {z : C | ∃ (i : Fin m) (g : G) (j : Fin 3) (w : C),
    ψ i w ∈ Set.range (if j = 2 then ProjectiveLine.infinity (Spec (.of K)) else
        AffineSpace.homOfVector (𝟙 (Spec (.of K))) (fun _ ↦ if j = 0 then 0 else 1) ≫
          ProjectiveLine.affineChart (Spec (.of K))) ∧ (σC g).hom w = z}

/-- The fibre-product lifting set, retaining the original group even for a nonfaithful action.
The theorem supplies its componentwise group structure and the two projection homomorphisms.
Source: de Jong (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model) -/
def orbitKummerLiftingPairs (G : Type v) [Group G] (F L : Type u) [Field F] [Field L]
    [MulSemiringAction G F] [Algebra F L] [Algebra (FixedPoints.subfield G F) L] :
    Set (G × (L ≃ₐ[FixedPoints.subfield G F] L)) :=
  {j | ∀ a : F, j.2 (algebraMap F L a) = algebraMap F L (j.1 • a)}

/-- The normalization map of the generic curve in the radical field, stated using relative
normalization to avoid an arbitrary identification of the two generic stalks.
Source: de Jong (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model) -/
noncomputable def orbitKummerGenericExtension {X S : Scheme.{u}}
    [IsIntegral S] [IsIntegral X] (f : X ⟶ S)
    [Algebra S.functionField X.functionField]
    (hKF : X.fromSpecFunctionField ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField X.functionField)) ≫
        S.fromSpecFunctionField)
    (L : Type u) [Field L] [Algebra X.functionField L] :
    Spec (.of L) ⟶ orbitKummerGenericCurve f :=
  Spec.map (CommRingCat.ofHom (algebraMap X.functionField L)) ≫
    orbitKummerGenericPoint f hKF
/-- The orbit Kummer field, its lifting group, constants and normal relative diagram.

Source: de Jong (1997), §3.5, pp.607--608.
(blueprint: lem-sfb-orbit-kummer-normal-model)

Proof:

1. Base change the projective morphism to $\operatorname{Spec}K$. Thus $C$ is projective, and its
assumed smoothness, geometric integrality and dimension make it a smooth projective integral
curve. Each generic pencil is surjective, so $x_i$ is nonconstant and $x_i,x_i-1$ are nonzero.
Automorphisms preserve nonzero elements. The zeros and poles of $x_i$ lie over $0,\infty$ and
those of $x_i-1$ over $1,\infty$. The same assertion after $g$ places every translated divisor in
the indicated union $D$. A reduced finite etale scheme over a field is a finite disjoint union of
spectra of finite separable residue fields. The reduced union of these translated point sets
therefore has this form as well and is finite etale. Semilinear translation changes the base by a
field isomorphism and preserves separability. Since $M$ is stable and each original point set
avoids it, so does $D$. In particular every root-list function and its inverse is regular on
$C\setminus D$.
Uses: lem-pc-projective-base-change, lem-weil-pbc-etale-fibre-discrete-separable-points, lem-exc-
etale-coproduct-etale.

2. Let $A$ be the finite list of translated functions, of length $r$. A primitive $\ell$th root
$\zeta\in K$ gives all roots $1,\zeta,\ldots,\zeta^{\ell-1}$ of $T^\ell-1$ in $F$: they are
distinct and account for its degree. Apply the multiradical lemma with $n=\ell$. It gives finite
Galois $L/F$ and $d=[L:F]\mid\ell^r$. In particular $d$ is invertible in $K$. Apply radical
normalization with $U=C\setminus D$ to get a normal integral projective $K$-curve $\widetilde C$,
finite surjective over $C$, etale over $U$, and with specified function field $L$. Apply tame
Galois curve normalization: its hypotheses are exactly the smoothness of $C$, the finite Galois
extension of invertible degree $d$, the reduced finite etale $D$, and the etaleness over $U$ just
obtained. Hence $\widetilde C$ is smooth over $K$.
Uses: lem-sfb-multiradical-galois-degree, lem-sfb-radical-normalization-projective-etale, lem-sfb-
tame-galois-curve-normalization-smooth.

3. Apply the smooth-cover constant-field marking lemma to $\widetilde C\to C$, the open
$U=C\setminus D$, and $M\subset U$. It identifies the algebraic constants in $L$ with
$E=\Gamma(\widetilde C,\mathcal O)$, proves $E/K$ finite separable, and supplies the canonical
$E$-structure. Over $E$ the curve is smooth projective geometrically integral with function field
$L$, and $\widetilde C\times_C M$ is reduced finite etale over $E$. It also gives $E\cap F=K$.
This uses the actual finite cover and its etale locus, rather than inferring smoothness from
normality over a possibly imperfect field.
Uses: lem-sfb-smooth-cover-constant-field-marking.

4. Apply the finite faithful action theorem to the image $H$ of $G\to\operatorname{Aut}(F)$. Its
fixed field is $B_0$, so $F/B_0$ is finite Galois; choose a primitive element $b$ for this finite
separable extension. The polynomial $P(T)=\prod_{h\in H}(T-h(b))\prod_{a\in A}(T^\ell-a)$ has
coefficients in $B_0$: $H$ permutes the first factors and $G$ permutes the root list in the second
product. It splits over $L$, since every root of $T^\ell-a$ is a chosen radical multiplied by a
power of $\zeta$. Its roots generate $L$ over $B_0$, because they include $b$ and all chosen
radicals. The splitting-field theorem therefore makes $L/B_0$ finite and normal. Separability
follows from $F/B_0$, $L/F$ and separable transitivity. Thus $L/B_0$ is finite Galois. Repeated
factors in $P$ cause no problem: its separability is not asserted or used.
Uses: lem-wf-finite-field-action-fixed-degree, lem-weil-pbc-finite-separable-extension-primitive-
element, lem-sfb-splitting-field-finite-normal, lem-zl-separable-permanence.

5. For $g\in G$, its restriction to $F$ fixes $B_0$. The normal intermediate-isomorphism lifting
theorem extends it to an automorphism $\tau$ of $L/B_0$. Thus $(g,\tau)\in J$ and $J\to G$ is
onto. Composition and inversion preserve the defining restriction condition, so $J$ is a subgroup
of $G\times\operatorname{Aut}_{B_0}(L)$; it is finite by finite Galois theory. Its kernel is
exactly the pairs $(1,\tau)$ with $\tau|_F=1$, giving $N=\operatorname{Aut}_F(L)$. Finite Galois
theory gives $L^N=F$. Each $\tau$ sends $K$ to $K$, hence preserves the set $E$ of elements
algebraic over $K$. Consequently $E^N=E\cap L^N=E\cap F=K$. This identifies the kernel using the
fibre-product group even when the original $G$-action has a kernel.
Uses: lem-sfb-normal-intermediate-isomorphism-lifts, lem-weil-pbc-finite-galois-fixed-field.

6. The composite $X\to S\to\operatorname{Spec}k$ is H-projective by composition. Apply the
semilinear finite normalization model first to $S$, the extension $E/K$, and the $J$-action just
constructed, and then to $X$, the extension $L/F$, and the action of $J$ on $X$ through $G$. This
gives the specified models $T=\operatorname{Nor}_E(S)$ and $Y=\operatorname{Nor}_L(X)$, their
canonical generic identifications, normality, integrality, projectivity and finite type over $k$,
and finite surjective maps $T\to S$, $Y\to X$. It also gives actions with field action exactly the
prescribed $J$-actions and compatible with their action on $k$.
Uses: lem-trf-h-projective-composition, lem-sfb-semilinear-finite-normalization-model.

7. The generic maps give $\operatorname{Spec}L\to X\times_ST$, and the latter scheme is integral
over $X$ because $T\to S$ is finite. Apply the relative-normalization universal property for
$\operatorname{Spec}L\to X$ to obtain $h:Y\to X\times_ST$ and hence $g:Y\to T$. This is the
normalization used here: its affine ring is the integral closure in $L$. The uniqueness clause
makes both maps $J$-equivariant, since their conjugates agree on $\operatorname{Spec}L$. The map
$h$ is finite. Indeed over $\operatorname{Spec}R\subset X$ the product is $\operatorname{Spec}B$
for a finite $R$-algebra $B$, and $Y$ is $\operatorname{Spec}C$ for a finite $R$-algebra $C$. The
factorization gives $B\to C$, and any finite set of $R$-module generators of $C$ also generates it
over $B$.
Uses: lem-sbc-relative-normalization-universal-property, lem-weil-pbc-finite-morphism-permanence.

8. We check surjectivity onto the full product $Z=X\times_ST$. The finite dominant map $T\to S$ is
universally open since $S$ is normal and locally Noetherian. Hence $Z\to X$ is open. Both schemes
are Noetherian of finite type over $k$, so $Z$ has finitely many irreducible components. Each
component has a nonempty open part avoiding the other components. Its image is nonempty open in
integral $X$ and contains the generic point $\eta_X$. Thus every component of $Z$ meets
$Z_{\eta_X}$. This fibre is $\operatorname{Spec}(F\otimes_K E)$. It is integral: choose a nonempty
affine $\operatorname{Spec}R\subset C$; geometric integrality says $R\otimes_K E$ is a domain, and
localization gives $F\otimes_K E$. It is a field since finite-dimensional over $F$. Thus
$Z_{\eta_X}$ has one point. The unique point of this fibre belongs to every chosen open part
avoiding the other components. If two components existed, the open part for the first would
exclude the point that belongs to the second. Thus there is exactly one component and $Z$ is
irreducible. The finite map $h$ has closed image and contains this point (the map from
$\operatorname{Spec}L$), hence is surjective.
Uses: lem-sfb-finite-dominant-normal-base-universally-open, lem-weil-pbc-finite-type-over-
noetherian, lem-sfb-finite-type-composition-base-change, lem-weil-pbc-noetherian-finitely-many-
components, def-pc-geometrically-irreducible, lem-sc-integral-function-field-affine-fraction, lem-
weil-pbc-finite-closed-map-finite-fibres.

9. Integral closure commutes with localization. Localizing the affine charts of $Y\to X$ along
nonzero elements of the base therefore identifies $Y\times_S\operatorname{Spec}K$ with the
normalization $\widetilde C$ of $C$ in $L$. The same chart calculation identifies
$T\times_S\operatorname{Spec}K$ with $\operatorname{Spec}E$. Hence
$Y\times_T\operatorname{Spec}E=\widetilde C$, with the canonical $E$-structure from its inclusion
into $L$. This generic fibre is nonempty and pure of dimension one, smooth projective and
geometrically integral by step 3. In particular $g$ is dominant. Apply the finite-curve-factor
lemma to $q:T\to S$, $\nu:Y\to X$, $g$ and the finite map $h$. All four schemes are integral
finite type, $f$ and $S/k$ are H-projective, $q,\nu$ are finite surjective, and the required
generic curve has just been identified. It gives H-projectivity of $g$ and pure one-dimensional
geometric fibres.
Uses: lem-weil-pbc-integral-closure-commutes-localization, lem-sfb-finite-curve-factor-projective-
pure.

10. Under the generic-fibre identification of step 9, the reduced generic inverse image of $M$ is
exactly $\widetilde C\times_C M$. Step 3 made it reduced finite etale over $E$. The
$J$-equivariance of the diagram and the $G$-stability of $M$ make this inverse image stable under
$J$. The projection to $G$ is the one already shown surjective, so the diagram lifts the original
actions. No step identified $G$ with its automorphism image: the image $H$ was used only to apply
the faithful fixed-field theorem, and the actual lifting group remains the fibre product $J$. Thus
all conclusions also hold for nonfaithful semilinear actions.
-/
theorem orbit_kummer_normal_model
    (k : Type u) [Field k] (S X : Scheme.{u}) [IsIntegral S] [IsIntegral X]
    (pS : S ⟶ Spec (.of k)) (pX : X ⟶ Spec (.of k))
    [IsHProjective pS] [LocallyOfFiniteType pS] [QuasiCompact pS]
    [LocallyOfFiniteType pX] [QuasiCompact pX]
    (hSnormal : IsNormalScheme S) (hXnormal : IsNormalScheme X)
    (f : X ⟶ S) [IsHProjective f] (hf : f ≫ pS = pX)
    (hpure : ∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
      (s : Spec (.of Ω') ⟶ S), (pullback f s).IsPureDimension 1)
    [Smooth (pullback.snd f S.fromSpecFunctionField)]
    [GeometricallyIntegral (pullback.snd f S.fromSpecFunctionField)]
    [Algebra S.functionField X.functionField]
    (hKF : X.fromSpecFunctionField ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap S.functionField X.functionField)) ≫
        S.fromSpecFunctionField)
    (G : Type v) [Group G] [Finite G]
    (σk : G →* (k ≃+* k)) (σX : G →* Aut X) (σS : G →* Aut S)
    [MulSemiringAction G X.functionField]
    (hGfield : ∀ (g : G) (a : X.functionField),
      g • a = (Scheme.functionFieldAut (σX g⁻¹)).hom a)
    (hGkX : ∀ g : G, (σX g).hom ≫ pX =
      pX ≫ Spec.map (CommRingCat.ofHom (σk g⁻¹).toRingHom))
    (hGkS : ∀ g : G, (σS g).hom ≫ pS =
      pS ≫ Spec.map (CommRingCat.ofHom (σk g⁻¹).toRingHom))
    (hGf : ∀ g : G, (σX g).hom ≫ f = f ≫ (σS g).hom)
    (σC : G →* Aut (orbitKummerGenericCurve f))
    (hCX : ∀ g : G, (σC g).hom ≫ pullback.fst f S.fromSpecFunctionField =
      pullback.fst f S.fromSpecFunctionField ≫ (σX g).hom)
    (hCK : ∀ g : G, (σC g).hom ≫ pullback.snd f S.fromSpecFunctionField =
      pullback.snd f S.fromSpecFunctionField ≫
        Spec.map (Scheme.functionFieldAut (σS g)).hom)
    (M : Closeds (orbitKummerGenericCurve f))
    (hMfinite : IsFinite ((Scheme.IdealSheafData.vanishingIdeal M).subschemeι ≫
      pullback.snd f S.fromSpecFunctionField))
    (hMetale : Etale ((Scheme.IdealSheafData.vanishingIdeal M).subschemeι ≫
      pullback.snd f S.fromSpecFunctionField))
    (hMstable : ∀ g : G, (σC g).hom '' (M : Set (orbitKummerGenericCurve f)) = M)
    (ell : ℕ) (hell : ell.Prime) (hell5 : 5 ≤ ell) (hchar : (ell : k) ≠ 0)
    (ζ : S.functionField) (hζ : IsPrimitiveRoot ζ ell)
    (m : ℕ) (U : Fin m → S.Opens) (hUaffine : ∀ i, IsAffineOpen (U i))
    (hUne : ∀ i, Nonempty (U i)) (hUcover : iSup U = ⊤)
    (φ : ∀ i : Fin m, pullback f (U i).ι ⟶ ProjectiveLine (U i).toScheme)
    (hφover : ∀ i, φ i ≫ ProjectiveLine (U i).toScheme ↘ (U i).toScheme =
      pullback.snd f (U i).ι)
    (hφfinite : ∀ i, IsFinite (φ i)) (hφsurj : ∀ i, Surjective (φ i))
    (e : ∀ i : Fin m, Spec S.functionField ⟶ (U i).toScheme)
    (he : ∀ i, e i ≫ (U i).ι = S.fromSpecFunctionField)
    (c : ∀ i : Fin m, orbitKummerGenericCurve f ⟶ pullback f (U i).ι)
    (hcX : ∀ i, c i ≫ pullback.fst f (U i).ι =
      pullback.fst f S.fromSpecFunctionField)
    (hcK : ∀ i, c i ≫ pullback.snd f (U i).ι =
      pullback.snd f S.fromSpecFunctionField ≫ e i)
    (ψ : Fin m → (orbitKummerGenericCurve f ⟶ ProjectiveLine (Spec S.functionField)))
    (hψover : ∀ i, ψ i ≫ ProjectiveLine (Spec S.functionField) ↘ Spec S.functionField =
      pullback.snd f S.fromSpecFunctionField)
    (hψφ : ∀ i, ψ i ≫ ProjectiveSpace.map (ULift.{u} (Fin 2)) (e i) = c i ≫ φ i)
    (hψetale : ∀ i, ∃ V : (ProjectiveLine (Spec S.functionField)).Opens,
      Dense (V : Set (ProjectiveLine (Spec S.functionField))) ∧ Etale ((ψ i) ∣_ V))
    (hspecial : ∀ (i : Fin m) (j : Fin 3),
      IsFinite (pullback.snd (ψ i)
        (if j = 2 then ProjectiveLine.infinity (Spec S.functionField) else
        AffineSpace.homOfVector (𝟙 (Spec S.functionField)) (fun _ ↦ if j = 0 then 0 else 1) ≫
          ProjectiveLine.affineChart (Spec S.functionField))) ∧
      Etale (pullback.snd (ψ i)
        (if j = 2 then ProjectiveLine.infinity (Spec S.functionField) else
        AffineSpace.homOfVector (𝟙 (Spec S.functionField)) (fun _ ↦ if j = 0 then 0 else 1) ≫
          ProjectiveLine.affineChart (Spec S.functionField))))
    (havoid : ∀ (i : Fin m) (j : Fin 3) (z : orbitKummerGenericCurve f),
      ψ i z ∈ Set.range (if j = 2 then ProjectiveLine.infinity (Spec S.functionField) else
        AffineSpace.homOfVector (𝟙 (Spec S.functionField)) (fun _ ↦ if j = 0 then 0 else 1) ≫
          ProjectiveLine.affineChart (Spec S.functionField)) → z ∉ M)
    (x : Fin m → X.functionField)
    (hx : ∀ i, orbitKummerGenericPoint f hKF ≫ ψ i =
      AffineSpace.homOfVector
        (Spec.map (CommRingCat.ofHom (algebraMap S.functionField X.functionField)))
        (fun _ ↦ (Scheme.ΓSpecIso X.functionField).inv (x i)) ≫
          ProjectiveLine.affineChart (Spec S.functionField))
    (Ω : Type u) [Field Ω] [Algebra X.functionField Ω] [IsAlgClosure X.functionField Ω]
    (L : IntermediateField X.functionField Ω) (hL : L = orbitKummerField G
      X.functionField Ω x ell)
    [Algebra S.functionField L] [IsScalarTower S.functionField X.functionField L]
    [Algebra (FixedPoints.subfield G X.functionField) L]
    (hBL : ∀ a : FixedPoints.subfield G X.functionField,
      algebraMap (FixedPoints.subfield G X.functionField) L a =
        algebraMap X.functionField L a.val)
    (E : IntermediateField S.functionField L) (hE : E = algebraicClosure S.functionField L)
    (D : Closeds (orbitKummerGenericCurve f)) (hD : D = orbitKummerBranchLocus G σC ψ) :
    (∀ (i : Fin m) (g : G) (b : Bool), orbitKummerRadicand G X.functionField x i g b ≠ 0) ∧
    (∀ z : orbitKummerGenericCurve f, z ∈ D ↔
      ∃ (i : Fin m) (g : G) (j : Fin 3) (w : orbitKummerGenericCurve f),
        ψ i w ∈ Set.range (if j = 2 then ProjectiveLine.infinity (Spec S.functionField) else
        AffineSpace.homOfVector (𝟙 (Spec S.functionField)) (fun _ ↦ if j = 0 then 0 else 1) ≫
          ProjectiveLine.affineChart (Spec S.functionField)) ∧
          (σC g).hom w = z) ∧
    IsFinite ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫
      pullback.snd f S.fromSpecFunctionField) ∧
    Etale ((Scheme.IdealSheafData.vanishingIdeal D).subschemeι ≫
      pullback.snd f S.fromSpecFunctionField) ∧
    Disjoint (D : Set (orbitKummerGenericCurve f)) (M : Set (orbitKummerGenericCurve f)) ∧
    (∀ (i : Fin m) (g : G) (b : Bool) (z : orbitKummerGenericCurve f), z ∉ D →
      ∃ (ι : (orbitKummerGenericCurve f).presheaf.stalk z →+* X.functionField)
        (a : (orbitKummerGenericCurve f).presheaf.stalk z),
        IsUnit a ∧
        Spec.map (CommRingCat.ofHom ι) ≫ (orbitKummerGenericCurve f).fromSpecStalk z =
          orbitKummerGenericPoint f hKF ∧
        ι a = orbitKummerRadicand G X.functionField x i g b) ∧
    Module.Finite X.functionField L ∧ IsGalois X.functionField L ∧
    Module.Finite (FixedPoints.subfield G X.functionField) L ∧
    IsGalois (FixedPoints.subfield G X.functionField) L ∧
    Module.Finite S.functionField E ∧ Algebra.IsSeparable S.functionField E ∧
    (∀ a : X.functionField, algebraMap X.functionField L a ∈ E ↔
      a ∈ Set.range (algebraMap S.functionField X.functionField)) ∧
    ∃ (pE : (orbitKummerGenericExtension f hKF L).normalization ⟶ Spec (.of E)),
      pE ≫ Spec.map (CommRingCat.ofHom (algebraMap S.functionField E)) =
        (orbitKummerGenericExtension f hKF L).fromNormalization ≫
          pullback.snd f S.fromSpecFunctionField ∧
      (orbitKummerGenericExtension f hKF L).toNormalization ≫ pE =
        Spec.map (CommRingCat.ofHom (algebraMap E L)) ∧
      Smooth ((orbitKummerGenericExtension f hKF L).fromNormalization ≫
        pullback.snd f S.fromSpecFunctionField) ∧
      Etale ((orbitKummerGenericExtension f hKF L).fromNormalization ∣_
        (⟨(D : Set (orbitKummerGenericCurve f))ᶜ, D.isClosed.isOpen_compl⟩)) ∧
      Smooth pE ∧ IsHProjective pE ∧ GeometricallyIntegral pE ∧
      ∃ (_ : Group (orbitKummerLiftingPairs G X.functionField L))
        (_ : Finite (orbitKummerLiftingPairs G X.functionField L))
        (β : orbitKummerLiftingPairs G X.functionField L →* G)
        (τ : orbitKummerLiftingPairs G X.functionField L →*
          (L ≃ₐ[FixedPoints.subfield G X.functionField] L))
        (τE : orbitKummerLiftingPairs G X.functionField L →* (E ≃+* E)),
        (∀ j, β j = j.val.1 ∧ τ j = j.val.2) ∧ Function.Surjective β ∧
        (∃ ε : β.ker ≃* (L ≃ₐ[X.functionField] L),
          ∀ (j : β.ker) (z : L), ε j z = τ j.val z) ∧
        (∀ z : L, z ∈ Set.range (algebraMap X.functionField L) ↔
          ∀ j : β.ker, τ j.val z = z) ∧
        (∀ (j : orbitKummerLiftingPairs G X.functionField L) (z : E),
          (τE j z : L) = τ j z) ∧
        (∀ z : E, z ∈ Set.range (algebraMap S.functionField E) ↔
          ∀ j : β.ker, τE j.val z = z) ∧
        ∃ (q : X.normalizationIn L ⟶ S.normalizationIn E)
          (r : X.normalizationIn L ⟶ pullback f (S.fromNormalizationIn E))
          (aT : orbitKummerLiftingPairs G X.functionField L →* Aut (S.normalizationIn E))
          (aY : orbitKummerLiftingPairs G X.functionField L →* Aut (X.normalizationIn L))
          (ηE : Spec (.of E) ⟶ S.normalizationIn E)
          (cY : (orbitKummerGenericExtension f hKF L).normalization ⟶ X.normalizationIn L),
          IsNormalScheme (S.normalizationIn E) ∧ IsNormalScheme (X.normalizationIn L) ∧
          IsHProjective (S.fromNormalizationIn E ≫ pS) ∧
          LocallyOfFiniteType (S.fromNormalizationIn E ≫ pS) ∧
          QuasiCompact (S.fromNormalizationIn E ≫ pS) ∧
          LocallyOfFiniteType (X.fromNormalizationIn L ≫ pX) ∧
          QuasiCompact (X.fromNormalizationIn L ≫ pX) ∧
          IsFinite (S.fromNormalizationIn E) ∧ Surjective (S.fromNormalizationIn E) ∧
          IsFinite r ∧ Surjective r ∧
          r ≫ pullback.fst f (S.fromNormalizationIn E) = X.fromNormalizationIn L ∧
          r ≫ pullback.snd f (S.fromNormalizationIn E) = q ∧
          IsHProjective q ∧
          (∀ (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
            (s : Spec (.of Ω') ⟶ S.normalizationIn E), (pullback q s).IsPureDimension 1) ∧
          ηE = (S.fromSpecOfAlgebraFunctionField E).toNormalization ∧
          cY ≫ X.fromNormalizationIn L =
            (orbitKummerGenericExtension f hKF L).fromNormalization ≫
              pullback.fst f S.fromSpecFunctionField ∧
          (orbitKummerGenericExtension f hKF L).toNormalization ≫ cY =
            (X.fromSpecOfAlgebraFunctionField L).toNormalization ∧
          cY ≫ q = pE ≫ ηE ∧ IsPullback cY pE q ηE ∧
          (∀ j, (aT j).hom ≫ S.fromNormalizationIn E =
            S.fromNormalizationIn E ≫ (σS (β j)).hom) ∧
          (∀ j, (aY j).hom ≫ X.fromNormalizationIn L =
            X.fromNormalizationIn L ≫ (σX (β j)).hom) ∧
          (∀ j, (aY j).hom ≫ q = q ≫ (aT j).hom) ∧
          (∀ j, Spec.map (CommRingCat.ofHom (τE j⁻¹).toRingHom) ≫ ηE =
            ηE ≫ (aT j).hom) ∧
          (∀ j, Spec.map (CommRingCat.ofHom (τ j⁻¹).toRingHom) ≫
            (X.fromSpecOfAlgebraFunctionField L).toNormalization =
              (X.fromSpecOfAlgebraFunctionField L).toNormalization ≫ (aY j).hom) ∧
          IsFinite (pullback.fst (orbitKummerGenericExtension f hKF L).fromNormalization
            (Scheme.IdealSheafData.vanishingIdeal M).subschemeι ≫ pE) ∧
          Etale (pullback.fst (orbitKummerGenericExtension f hKF L).fromNormalization
            (Scheme.IdealSheafData.vanishingIdeal M).subschemeι ≫ pE) ∧
          ∃ aC : orbitKummerLiftingPairs G X.functionField L →*
            Aut (orbitKummerGenericExtension f hKF L).normalization,
            (∀ j, (aC j).hom ≫ cY = cY ≫ (aY j).hom) ∧
            (∀ j, (aC j).hom ≫ pE =
              pE ≫ Spec.map (CommRingCat.ofHom (τE j⁻¹).toRingHom)) ∧
            (∀ j, (aC j).hom ≫ (orbitKummerGenericExtension f hKF L).fromNormalization =
              (orbitKummerGenericExtension f hKF L).fromNormalization ≫ (σC (β j)).hom) ∧
            (∀ j, (aC j).hom ''
              ((orbitKummerGenericExtension f hKF L).fromNormalization ⁻¹'
                (M : Set (orbitKummerGenericCurve f))) =
              (orbitKummerGenericExtension f hKF L).fromNormalization ⁻¹'
                (M : Set (orbitKummerGenericCurve f))) := by
  sorry

end AlgebraicGeometry
