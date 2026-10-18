/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q105
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.Sober
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Algebraic.Defs
import Sheaf.FieldTheory.FiniteRelativeAlgebraicClosure
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Sheaf.Compactification.NagataSketchClosure
import Sheaf.RingTheory.CompleteLocalExcellent
import Sheaf.RingTheory.IsExcellentFiniteTypeLocalization
import Sheaf.AlgebraicGeometry.ExcellentSchemeAffineCover
import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
import Sheaf.AlgebraicGeometry.ExcellentNormalizationPreparation
import Sheaf.AlgebraicGeometry.RegularNormalDecomposition
import WeilConjectures.Mathlib.AlgebraicGeometry.FunctionField
import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
import Sheaf.AlgebraicGeometry.Morphisms.FiniteProjectiveBundle
import Sheaf.AlgebraicGeometry.ProjectiveBundleToHProjective
import Sheaf.AlgebraicGeometry.Morphisms.HProjectiveComposition
import Sheaf.RingTheory.IntegralComponentHenselianPermanence
import Sheaf.RingTheory.FiniteOverCompleteLocalProduct
import Sheaf.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import WeilConjectures.AlgebraicGeometry.Regular
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Sheaf.FieldTheory.FieldExtensionGeometricallyIrreducible
import Sheaf.AlgebraicGeometry.GenericPointGeometricIrreducibility

/-!
# Normal projective compactification over a complete trait

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI, section 3.7,
first paragraph, printed p.254; Stacks Project Tags 01WA, 035S, 035Q.
(blueprint: lem-per-normal-projective-compactification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A regular integral flat quasi-projective scheme over a complete strictly henselian
mixed-characteristic trait embeds densely in a normal integral projective scheme over the
finite trait of algebraic constants. The original scheme and its function field are retained.
The three generic-point commutativities identify all field maps with the structural maps.
Source: ILO, Expose XVI, section 3.7, first paragraph, printed p.254; Stacks 01WA, 035S, 035Q.
(blueprint: lem-per-normal-projective-compactification).

Proof:
1. Write $F=k(X)$. Let $\xi$ be the generic point of the nonempty integral scheme $X$ and $s$ its
image in $S$. Flatness at $\xi$ [def-weil-flat-morphism] says that $F=\mathcal O_{X,\xi}$ is flat
over $\mathcal O_{S,s}$, which is $R$ (if $s$ is the closed point) or $K$ (if $s$ is the generic
point). In the first case [lem-trf-flat-module-torsionfree-domain] shows that nonzero elements of
$R$ act injectively on the nonzero field $F$; in the second case they act through units of $K$. In
both cases nonzero elements of $R$ act injectively on $F$. Thus $R\hookrightarrow F$ and
$K\hookrightarrow F$. On a nonempty affine finite-type chart of $X$, the generic prime contracts
to $(0)\subset R$, so [lem-weil-pbc-finite-type-residue-field-extension-finitely-generated] gives
that $F/K$ is finitely generated. Let $L$ be the subfield of elements of $F$ algebraic over $K$.
By [lem-zl-finite-algebraic-closure], $L/K$ is finite. Mixed characteristic gives characteristic
zero, so [lem-weil-pbc-char-zero-field-extension-separable] makes this finite extension separable.

2. Choose the locally closed immersion $X\hookrightarrow\mathbf P^n_S$ in the quasi-projectivity
hypothesis. It is quasi-compact: $X$ is Noetherian by [lem-weil-pbc-finite-type-over-noetherian],
hence each open subset of $X$ is quasi-compact. Projective space is separated over the affine $S$
by [lemma-nagata-projective-space-base-change-proper] and the definition of properness. Apply
[sk-lem-nagata-sketch-closure] to form its scheme-theoretic image $Y\hookrightarrow\mathbf P^n_S$.
It gives an open immersion $X\hookrightarrow Y$ which is schematically dense. The underlying space
of $Y$ is the closure of the irreducible $X$, hence irreducible. For any nonempty affine open
$V\subset Y$, schematic density injects $\mathcal O_Y(V)$ into $\mathcal O_X(V\cap X)$, which
embeds in $F$; thus this ring is a domain. Therefore $Y$ is integral, $X$ is dense in it, and
$k(Y)=F$. Its displayed closed immersion makes $Y\to S$ projective.

3. The complete Noetherian local ring $R$ is excellent by [lem-per-complete-local-excellence]. On
each standard affine projective chart the ring of $Y$ is a quotient of $R[t_1,\ldots,t_n]$, so $Y$
is finite type over $S$ and is Noetherian by [lem-weil-pbc-finite-type-over-noetherian]. These
chart rings are finite-type $R$-algebras and are excellent by
[lem-exc-finite-type-localization-excellent]. Since $Y$ is covered by these affine opens,
[lem-trf-excellent-scheme-affine-cover] makes the coordinate ring of every affine open of $Y$
excellent, which is the excellence hypothesis of the preparation node. Form the normalization
$\nu:C=Y^\nu\to Y$ in $F$ using [def-sc-normalization]. Since $Y$ is reduced, excellent and
Noetherian, [lem-per-excellent-normalization-preparation] gives that $\nu$ is finite and
surjective and $C$ is normal and Noetherian. The componentwise normalization has one component
here: on any nonempty affine chart its ring is the integral closure of a domain in $F$, hence a
domain. Thus $C$ is integral and $k(C)=F$.

4. Regularity of $X$ implies normality by [rem-pc-regular-normal]. We check the normalization over
the entire original open, not just over an unspecified dense open. If $A=\mathcal O_X(U)$ for a
nonempty affine open $U\subset X$, an element of $F$ integral over $A$ is integral over every
local ring $\mathcal O_{X,x}$ for $x\in U$; normality places it in every such local ring. By
[lem-sc-function-field-sections-glue] it belongs to $A$, so $A$ is integrally closed in $F$. On a
chart of $Y$ the normalization is integral closure in $F$;
[lem-weil-pbc-integral-closure-commutes-localization] identifies its restriction to each principal
open with the integral closure of that open. Principal opens of charts of $Y$ contained in $X$
cover $X$. The preceding equality therefore shows $\nu^{-1}X\cong X$ over $Y$. Its inverse gives a
dense open immersion $j:X\hookrightarrow C$, and the induced function-field identification is
$k(C)=k(X)=F$.

5. The projective embedding $Y\hookrightarrow\mathbf P^n_S$, with affine $S$, supplies an ample
invertible sheaf on $Y$ by [lem-weil-pbc-projective-ample-invertible]. The finite map $\nu:C\to Y$
is projective in the projective-bundle convention by [lem-trf-finite-projective-bundle]. Because
$Y$ has the stated ample sheaf, [lem-trf-projective-bundle-to-h-projective] upgrades this to the
finite-projective-space convention. Apply [lem-trf-h-projective-composition] to $C\to Y\to S$.
Hence $C\to S$ is projective in exactly the convention required in the item.

6. Let $R_0$ be the integral closure of $R$ in the finite separable extension $L/K$. By
[lem-weil-pbc-noetherian-normal-separable-integral-closure-finite], $R_0$ is finite over $R$. By
[lem-weil-pbc-integral-closure-finite-extension-normal], it is a normal domain with fraction field
$L$. The ring $R$ is henselian and strictly henselian by hypothesis. Since a domain has only the
idempotents $0,1$, [lem-trf-integral-component-henselian-permanence] gives that $R_0$ is local and
strictly henselian. By [lem-weil-pbc-finite-over-complete-local-product] it is complete Noetherian
local. Finally [lem-sc-integral-closure-dedekind-surjective-fibres] gives that $R_0$ has dimension
one, so [lem-sc-normal-dim1-dvr] makes it a discrete valuation ring. Set
$S_0=\operatorname{Spec}R_0$. The inclusion $R\subset R_0$ gives a finite dominant extension of
complete strictly henselian traits, with fraction field $k(S_0)=L$.

7. For each $a\in R_0\subset L\subset F$ and every $c\in C$, a monic equation over $R$ is also a
monic equation over the local ring $\mathcal O_{C,c}\subset F$. Because $C$ is normal,
$a\in\mathcal O_{C,c}$. Apply [lem-sc-function-field-sections-glue] on $C$: $a$ is a global
section. These sections are unique, since sections of the integral $C$ inject into $F$, and
addition, multiplication and the $R$-algebra structure agree in $F$. Thus they define an
$R$-algebra map $R_0\to\Gamma(C,\mathcal O_C)$. The natural affine-spectrum adjunction
[lem-a1-locally-ringed-space-affine-adjunction] yields a morphism $q:C\to S_0$ whose composite
with $S_0\to S$ is the structural morphism already constructed. Restricting $q$ along $j$ gives
the factorization on $X$ as well. This changes the base of the structural map only: $X$ itself has
not been replaced by a fibre product.

8. The finite morphism $S_0\to S$ is separated by [lem-weil-pbc-finite-closed-map-finite-fibres].
Step 5 made the composite $C\xrightarrow qS_0\to S$ H-projective. Apply
[lem-per-h-projective-permanence] to this factorization. It gives a closed immersion
$C\hookrightarrow\mathbf P^N_{S_0}$ over $S_0$, so $C$ is projective over $S_0$ without changing
its scheme or function field.

9. The inclusion $R_0\subset F$ is the map on generic stalks of $q$. Every local ring of the
integral $C$ is a subring of $F$, so its $R_0$-module is torsion-free: $ab=0$ with $a\ne0$ implies
$b=0$ in $F$. A discrete valuation ring is a valuation ring, and
[lem-trf-valuation-torsionfree-flat] therefore makes each of these local rings flat over $R_0$. At
a point over the closed point of $S_0$ this is precisely flatness over the base local ring $R_0$.
At a point over the generic point the base local ring is $L$, and any vector space over a field is
flat. Thus $q$ is flat at every point, as required.

10. Let $C_L$ be the generic fibre of $q$. It is nonempty, integral, and has function field $F$:
on affine charts it is obtained by localizing the domains of $C$ at $R_0\setminus\{0\}$. It is
finite type over $L$, for the projective embedding in Step 8 gives a finite affine cover by
quotients of polynomial $L$-algebras. The field $L$, being algebraic over the characteristic-zero
$K$, has characteristic zero, hence is perfect. Apply [lem-kun-geometric-reduced-perfect] to the
reduced finite-type $L$-scheme $C_L$; it is geometrically reduced. Also $L$ is algebraically
closed in $F$: any element of $F$ algebraic over $L$ is algebraic over $K$ by transitivity of
algebraicity and hence lies in $L$ by its definition. By
[lem-zl-field-extension-algebraically-closed-geometric], $\operatorname{Spec}F$ is geometrically
irreducible over $L$. Then [lem-zl-generic-point-geometric-irreducibility] makes $C_L$
geometrically irreducible. After any field extension it is both reduced and irreducible, hence
integral. This proves geometric integrality. Together with Steps 4 and 6 this gives all
assertions, including $k(C)=k(X)$ and $k(S_0)=L$ with no extension of $F$.
-/
theorem exists_normal_projective_compactification_over_complete_trait
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsStrictlyHenselianLocalRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [CharZero R] (hMixed : ringChar (IsLocalRing.ResidueField R) ≠ 0)
    (X : Scheme.{u}) [IsIntegral X] (hRegular : IsRegularScheme X)
    (f : X ⟶ Spec (.of R)) [Flat f] [LocallyOfFiniteType f] [QuasiCompact f]
    (hQuasiProjective : ∃ (ι : Type u) (_ : Finite ι)
      (i : X ⟶ ℙ(ι; Spec (.of R))),
      IsImmersion i ∧ i ≫ ℙ(ι; Spec (.of R)) ↘ Spec (.of R) = f) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : IsDomain R₀)
      (_ : IsDiscreteValuationRing R₀) (_ : IsStrictlyHenselianLocalRing R₀)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal R₀) R₀)
      (t : Spec (.of R₀) ⟶ Spec (.of R)),
      IsFinite t ∧ IsDominant t ∧
      ∃ (C : Scheme.{u}) (_ : IsIntegral C) (q : C ⟶ Spec (.of R₀)) (j : X ⟶ C),
        (∀ c : C, IsDomain (C.presheaf.stalk c) ∧
          IsIntegrallyClosed (C.presheaf.stalk c)) ∧
        IsHProjective q ∧ Flat q ∧ IsOpenImmersion j ∧ DenseRange j ∧
        j ≫ q ≫ t = f ∧
        GeometricallyIntegral (pullback.snd q
          ((Spec (.of R₀)).fromSpecStalk (genericPoint (Spec (.of R₀))))) ∧
        ∃ (e : C.functionField ≃+* X.functionField)
          (a : (Spec (.of R)).functionField →+* X.functionField)
          (b : (Spec (.of R₀)).functionField →+* X.functionField),
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫
              C.fromSpecStalk (genericPoint C) =
            X.fromSpecStalk (genericPoint X) ≫ j ∧
          Spec.map (CommRingCat.ofHom a) ≫
              (Spec (.of R)).fromSpecStalk (genericPoint (Spec (.of R))) =
            X.fromSpecStalk (genericPoint X) ≫ f ∧
          Spec.map (CommRingCat.ofHom b) ≫
              (Spec (.of R₀)).fromSpecStalk (genericPoint (Spec (.of R₀))) =
            X.fromSpecStalk (genericPoint X) ≫ j ≫ q ∧
          ∀ z : X.functionField,
            @IsAlgebraic (Spec (.of R)).functionField X.functionField _ _ a.toAlgebra z ↔
              z ∈ Set.range b := by
  sorry

end AlgebraicGeometry
