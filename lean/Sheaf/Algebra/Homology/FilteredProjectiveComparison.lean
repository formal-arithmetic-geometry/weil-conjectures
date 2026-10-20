/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import WeilConjectures.CategoryTheory.Abelian.Filtration
public import Sheaf.Algebra.Homology.TwoStepFilteredModuleDerived
public import Sheaf.Algebra.Homology.FiniteFilteredModuleHomotopy
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-!
# Filtered projective comparison

Source: Stacks Project, Derived Categories, Tags 03TB and 03TJ; the bounded-above
filtered K-projective comparison and its two-step specialization
(blueprint: lem-trf-filtered-projective-comparison).

## Main definitions

* `IsBoundedAbove` and `IsGradedProjective` record the two hypotheses on a filtered
  complex used by the comparison.
* `filteredDerivedCategory` and `boundedAboveFilteredDerivedCategory` are the
  unrestricted and bounded-above filtered localizations.
* `twoStepToFiniteComplex` embeds the existing two-step category using steps 0, 1, 2.
* `twoStepToFilteredDerived` is its canonical localization lift.

## Main statement

* `filteredProjectiveComparison` states the projective replacement, Hom comparison,
  and two-step compatibility assertions.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable (R : Type u) [CommRing R]

/-- A globally finite filtered module complex is bounded above when all terms above
some integer are zero.

Source: Stacks Project, Derived Categories, Tag 03TB;
(blueprint: lem-trf-filtered-projective-comparison). -/
def IsBoundedAbove (K : FiniteFilteredModuleHomotopy R) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N < n → IsZero (K.as.obj.obj.X n)

/-- Every associated graded module of a filtered complex is projective.

Source: Stacks Project, Derived Categories, Tag 03TB;
(blueprint: lem-trf-filtered-projective-comparison). -/
def IsGradedProjective (K : FiniteFilteredModuleHomotopy R) : Prop :=
  ∀ p n : ℤ, Module.Projective R ((K.as.obj.filtration.gradedPiece p).X n : Type u)

/-- The bounded-above full subcategory of the finite filtered homotopy category.

Source: Stacks Project, Derived Categories, Tag 03TB;
(blueprint: lem-trf-filtered-projective-comparison). -/
abbrev BoundedAboveFilteredHomotopy :=
  ObjectProperty.FullSubcategory (IsBoundedAbove R)

/-- The projective full subcategory inside bounded-above filtered homotopy objects.

Source: Stacks Project, Derived Categories, Tag 03TB;
(blueprint: lem-trf-filtered-projective-comparison). -/
def IsGradedProjectiveBounded (K : BoundedAboveFilteredHomotopy R) : Prop :=
  IsGradedProjective R K.obj

/-- The full subcategory of bounded-above filtered homotopy objects with projective
associated graded modules.

Source: Stacks Project, Derived Categories, Tag 03TB;
(blueprint: lem-trf-filtered-projective-comparison). -/
abbrev BoundedAboveGradedProjectiveHomotopy :=
  ObjectProperty.FullSubcategory (IsGradedProjectiveBounded R)

/-- Filtered quasi-isomorphisms among bounded-above filtered homotopy objects.

Source: Stacks Project, Derived Categories, Tag 03TB;
(blueprint: lem-trf-filtered-projective-comparison). -/
def boundedAboveFilteredQuasiIso :
    MorphismProperty (BoundedAboveFilteredHomotopy R) :=
  fun {_ _} f ↦ finiteFilteredModuleQuasiIso R f.hom

/-- The unrestricted filtered derived category, obtained by localizing globally finite
filtered homotopy objects at graded quasi-isomorphisms.

Source: Stacks Project, Derived Categories, Tags 05S1 and 05S2;
(blueprint: lem-trf-filtered-projective-comparison). -/
abbrev filteredDerivedCategory :=
  MorphismProperty.Localization (finiteFilteredModuleQuasiIso R)

/-- The bounded-above filtered derived category, obtained by localizing bounded-above
filtered homotopy objects at graded quasi-isomorphisms.

Source: Stacks Project, Derived Categories, Tag 03TB;
(blueprint: lem-trf-filtered-projective-comparison). -/
abbrev boundedAboveFilteredDerivedCategory :=
  MorphismProperty.Localization (boundedAboveFilteredQuasiIso R)

/-- The canonical functor from bounded-above graded-projective filtered homotopy objects
to the bounded-above filtered localization.

Source: Stacks Project, Derived Categories, Tag 03TB;
(blueprint: lem-trf-filtered-projective-comparison). -/
noncomputable def boundedProjectiveLocalizationFunctor :
    BoundedAboveGradedProjectiveHomotopy R ⥤ boundedAboveFilteredDerivedCategory R :=
  (ObjectProperty.ι (IsGradedProjectiveBounded R)) ⋙
    MorphismProperty.Q (boundedAboveFilteredQuasiIso R)

/-- The normalized filtration steps of a pair: whole in indices at most zero, the
specified subcomplex at one, and zero thereafter.
Source: Stacks, Tags 0121 and 03TB; blueprint two-step convention
(blueprint: lem-trf-filtered-projective-comparison). -/
noncomputable def twoStepFiltrationStep (K : TwoStepModuleComplex R) (p : ℤ) :
    Subobject K.obj.right :=
  if p ≤ 0 then ⊤ else if p = 1 then @Subobject.mk _ _ _ _ K.obj.hom K.property else ⊥

/-- The normalized steps decrease.
Source: Stacks, Tag 0121; blueprint two-step convention.
Proof: split into indices at most zero, index one, and indices at least two;
the only nontrivial comparisons are with the whole and zero subobjects.
(blueprint: lem-trf-filtered-projective-comparison). -/
theorem twoStepFiltrationStep_succ_le (K : TwoStepModuleComplex R) (p : ℤ) :
    twoStepFiltrationStep R K (p + 1) ≤ twoStepFiltrationStep R K p := by
  sorry

/-- The actual subcomplex filtration attached to a pair.
Source: Stacks, Tags 0121 and 03TB; blueprint two-step convention
(blueprint: lem-trf-filtered-projective-comparison). -/
noncomputable def twoStepFiltration (K : TwoStepModuleComplex R) :
    DecreasingFiltration K.obj.right where
  F := twoStepFiltrationStep R K
  F_succ_le := twoStepFiltrationStep_succ_le R K

/-- The normalized pair filtration has uniform endpoints zero and two.
Source: Stacks, Tags 0121 and 03TB; blueprint two-step convention.
Proof: the defining cases give the whole subobject at zero and the zero subobject at two.
(blueprint: lem-trf-filtered-projective-comparison). -/
theorem twoStepFiltration_isFinite (K : TwoStepModuleComplex R) :
    (twoStepFiltration R K).IsFinite := by
  sorry

/-- The globally finite filtered complex of a pair, with its actual total complex.
Source: Stacks, Tags 0121 and 03TB; blueprint two-step convention
(blueprint: lem-trf-filtered-projective-comparison). -/
noncomputable def twoStepFiniteComplex (K : TwoStepModuleComplex R) :
    FiniteFilteredModuleComplex R :=
  ⟨⟨K.obj.right, twoStepFiltration R K⟩, twoStepFiltration_isFinite R K⟩

/-- A square of pairs preserves the normalized subcomplex filtrations.
Source: Stacks, Tags 0121 and 03TB; blueprint two-step convention.
Proof: at one use the left component of the square, transported through the canonical
isomorphisms between a mono's domain and its subobject representative. At the whole and
zero steps use the total map and the zero map, respectively.
(blueprint: lem-trf-filtered-projective-comparison). -/
theorem twoStepFiniteComplex_preserves {K L : TwoStepModuleComplex R} (f : K ⟶ L) :
    ∀ p : ℤ, ∃ lift :
      ((twoStepFiltration R K).step p : CochainComplex (ModuleCat.{u} R) ℤ) ⟶
        ((twoStepFiltration R L).step p : CochainComplex (ModuleCat.{u} R) ℤ),
      lift ≫ ((twoStepFiltration R L).step p).arrow =
        ((twoStepFiltration R K).step p).arrow ≫ f.hom.right := by
  sorry

/-- Inclusion of pairs into globally finite filtered complexes, normalized on total maps.
Source: Stacks, Tags 0121 and 03TB; blueprint two-step convention
(blueprint: lem-trf-filtered-projective-comparison). -/
noncomputable def twoStepToFiniteComplex :
    TwoStepModuleComplex R ⥤ FiniteFilteredModuleComplex R where
  obj := twoStepFiniteComplex R
  map f := ObjectProperty.homMk ⟨f.hom.right, twoStepFiniteComplex_preserves R f⟩

/-- Pair homotopies become filtered homotopies under the normalized embedding.
Source: Stacks, Tags 03TB and 05S2; blueprint two-step convention.
Proof: retain the total homotopy. Transport its prescribed restrictions through the
canonical subobject representatives at one; all other steps are whole or zero. The
filtered homotopy quotient therefore identifies the images of the two maps.
(blueprint: lem-trf-filtered-projective-comparison). -/
theorem twoStepToFiniteComplex_homotopy (K L : TwoStepModuleComplex R)
    (f g : K ⟶ L) (h : twoStepModuleHomotopyRel R f g) :
    (twoStepToFiniteComplex R ⋙ finiteFilteredModuleHomotopyQuotient R).map f =
      (twoStepToFiniteComplex R ⋙ finiteFilteredModuleHomotopyQuotient R).map g := by
  sorry

/-- The normalized pair inclusion on homotopy categories.
Source: Stacks, Tags 03TB and 05S2; blueprint two-step convention
(blueprint: lem-trf-filtered-projective-comparison). -/
noncomputable def twoStepToFiniteHomotopy :
    TwoStepModuleHomotopy R ⥤ FiniteFilteredModuleHomotopy R :=
  CategoryTheory.Quotient.lift (twoStepModuleHomotopyRel R)
    (twoStepToFiniteComplex R ⋙ finiteFilteredModuleHomotopyQuotient R)
    (twoStepToFiniteComplex_homotopy R)

/-- Boundedness above for the total complex of a pair.
Source: Stacks, Tag 03TB (blueprint: lem-trf-filtered-projective-comparison). -/
def IsTwoStepBoundedAbove (K : TwoStepModuleHomotopy R) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N < n → IsZero (K.as.obj.right.X n)

/-- Projectivity of both graded modules of a pair in every cochain degree.
Source: Stacks, Tag 03TB (blueprint: lem-trf-filtered-projective-comparison). -/
def IsTwoStepGradedProjective (K : TwoStepModuleHomotopy R) : Prop :=
  ∀ b : Bool, ∀ n : ℤ,
    Module.Projective R (((twoStepGradedComplex R b).obj K.as).X n : Type u)

/-- The bounded-above two-step filtered homotopy category.
Source: Stacks, Tag 03TB (blueprint: lem-trf-filtered-projective-comparison). -/
abbrev TwoStepBoundedAboveFilteredHomotopy :=
  ObjectProperty.FullSubcategory (IsTwoStepBoundedAbove R)

/-- Graded quasi-isomorphisms among bounded-above pairs, using both recorded graded functors.
Source: Stacks, Tag 03TB (blueprint: lem-trf-filtered-projective-comparison). -/
def twoStepBoundedAboveFilteredQuasiIso :
    MorphismProperty (TwoStepBoundedAboveFilteredHomotopy R) :=
  fun {_ _} f ↦ twoStepModuleQuasiIso R f.hom

/-- The bounded-above two-step filtered derived category.
Source: Stacks, Tag 03TB (blueprint: lem-trf-filtered-projective-comparison). -/
abbrev twoStepBoundedAboveFilteredDerivedCategory :=
  MorphismProperty.Localization (twoStepBoundedAboveFilteredQuasiIso R)

/-- The projective full subcategory inside bounded-above pairs.
Source: Stacks, Tag 03TB (blueprint: lem-trf-filtered-projective-comparison). -/
def IsGradedProjectiveTwoStepBounded (K : TwoStepBoundedAboveFilteredHomotopy R) : Prop :=
  IsTwoStepGradedProjective R K.obj

/-- The bounded-above graded-projective two-step homotopy category.
Source: Stacks, Tag 03TB (blueprint: lem-trf-filtered-projective-comparison). -/
abbrev TwoStepBoundedAboveGradedProjectiveHomotopy :=
  ObjectProperty.FullSubcategory (IsGradedProjectiveTwoStepBounded R)

/-- The canonical two-step bounded-above graded-projective localization functor.
Source: Stacks, Tag 03TB (blueprint: lem-trf-filtered-projective-comparison). -/
noncomputable def twoStepBoundedProjectiveLocalizationFunctor :
    TwoStepBoundedAboveGradedProjectiveHomotopy R ⥤
      twoStepBoundedAboveFilteredDerivedCategory R :=
  (ObjectProperty.ι (IsGradedProjectiveTwoStepBounded R)) ⋙
    MorphismProperty.Q (twoStepBoundedAboveFilteredQuasiIso R)

/-- The pair inclusion sends its denominators to isomorphisms in the global localization.
Source: Stacks, Tags 03TB and 05S2; blueprint two-step comparison.
Proof: choose the pair-chain-map representative. Its normalized graded complexes are
canonically the quotient at zero, the subcomplex at one, and zero at all other indices.
The two assumed quasi-isomorphisms therefore give every graded quasi-isomorphism; the
homotopy inclusion preserves the representative, and global localization inverts it.
(blueprint: lem-trf-filtered-projective-comparison). -/
theorem twoStepToFiniteHomotopy_inverts :
    (twoStepModuleQuasiIso R).IsInvertedBy
      (twoStepToFiniteHomotopy R ⋙ MorphismProperty.Q (finiteFilteredModuleQuasiIso R)) := by
  sorry

/-- The canonical localization lift of the normalized pair inclusion.
Source: Stacks, Tags 03TB and 03TJ; blueprint two-step comparison
(blueprint: lem-trf-filtered-projective-comparison). -/
noncomputable def twoStepToFilteredDerived :
    TwoStepModuleDerived R ⥤ filteredDerivedCategory R :=
  CategoryTheory.Localization.Construction.lift
    (twoStepToFiniteHomotopy R ⋙ MorphismProperty.Q (finiteFilteredModuleQuasiIso R))
    (twoStepToFiniteHomotopy_inverts R)

/-- Filtered projective comparison: bounded-above filtered complexes admit bounded-above
filtered-projective replacements; maps from such replacements into arbitrary filtered
complexes are represented uniquely by filtered chain maps modulo filtered homotopy; and
all assertions, including the two-step restriction and its comparison with the global
filtered localization, remain valid.

Source: Stacks Project, Derived Categories, Tag 03TB (bounded-above projective comparison)
and Tag 03TJ (fully faithful bounded finite-projective models in unrestricted DF);
the unrestricted-target and two-step strengthening is the filtered K-projective extension
used in the blueprint (blueprint: lem-trf-filtered-projective-comparison).

Proof, following the nine steps of the node.
1. First establish the module-level lifting used below. Call a filtered surjection $v:B\to C$
   strict if $v(F^pB)=F^pC$ for every $p$. A finite filtered module $P$ with projective graded
   modules splits as a filtered module: choose sections of each surjection
   $F^pP\to\operatorname{gr}^pP$, using the lifting characterization of projectivity, and proceed
   downwards through the finite filtration. Thus $P\cong\bigoplus_{a\le p<b}P_p$, with
   $P_p\cong\operatorname{gr}^pP$ and $F^rP=\bigoplus_{p\ge r}P_p$. A filtered map $P\to C$ lifts
   along a strict filtered surjection $B\to C$: lift its restriction on each projective $P_p$
   along the surjection $F^pB\to F^pC$, then add these finitely many lifts. Also every filtered
   module $M$ with bounds $a,b$ admits a strict filtered surjection from a filtered free module.
   Take the free module $U(M)$ on the set of pairs $(p,x)$ with $a\le p<b$ and $x\in F^pM$, let
   $F^rU(M)$ be spanned by pairs with $p\ge r$, and send the basis vector $(p,x)$ to $x$. For
   $a\le r<b$ the vectors $(r,x)$ lift all $x\in F^rM$; the cases $r<a$ and $r\ge b$ are
   immediate. Its $p$-th graded module is free on the pairs of weight exactly $p$, hence
   projective. These statements use arbitrary free modules, with no finite-generation assumption.
   Dependencies: def-sp-filtration, def-weil-pbc-projective-module, def-weil-pbc-free-module,
   lem-weil-pbc-free-module-projective.
2. Now construct the replacement, rather than applying the omitted assertion of Tag 03TB. Fix
   $K^j=0$ for $j>c$ and global filtration bounds $a,b$. Put $Q^j=0$ above $c$ and construct
   $q:Q\to K$ downwards. At stage $n\le c$, suppose all terms and maps in degrees $j>n$ have been
   constructed, $q^j$ is a strict filtered surjection there, and, writing $N^j=\ker q^j$ with the
   induced filtration, every complex $F^pN$ is exact in degrees $j>n+1$. Define the filtered
   module $$B^n=\{(k,x)\in K^n\oplus Q^{n+1}:d_Kk=q^{n+1}x,\ d_Qx=0\},\qquad
   F^pB^n=B^n\cap(F^pK^n\oplus F^pQ^{n+1}).$$ The projection $B^n\to K^n$ is strict and
   surjective. Indeed, for $k\in F^pK^n$, choose $x_0\in F^pQ^{n+1}$ lifting $d_Kk$. Then
   $d_Qx_0\in F^pN^{n+2}$ is a cycle; the induction hypothesis gives $y\in F^pN^{n+1}$ with
   $d_Qy=d_Qx_0$. Put $x=x_0-y$. Choose the strict filtered free cover $Q^n=U(B^n)\to B^n$ from
   step 1 and define $q^n,d_Q^n$ by its two projections. The equations defining $B^n$ give
   $q^{n+1}d_Q^n=d_Kq^n$ and $d_Q^{n+1}d_Q^n=0$, and $q^n$ is strict surjective. For a cycle $x\in
   F^pN^{n+1}$, the pair $(0,x)\in F^pB^n$ lifts to $z\in F^pQ^n$ with $q^nz=0$ and $d_Qz=x$. Thus
   $F^pN$ is now exact in degree $n+1$, establishing the next induction hypothesis. Above $c$ all
   objects are zero, so the initial hypotheses hold. Induction on $c-n$ constructs all degrees,
   with the same $a,b$ in every degree; no limiting operation on modules is involved.
   Dependencies: def-weil-abstract-derived-category, def-sp-filtration.
3. The construction gives a filtered quasi-isomorphism $q:Q\to K$. For each integer $p$, $F^pN$ is
   acyclic, because its exactness in any fixed degree is established at a finite stage of step 2.
   Consequently $\operatorname{gr}^pN$ is acyclic as well: represent a graded cycle by $z\in
   F^pN^n$, so $dz\in F^{p+1}N^{n+1}$; exactness there gives $w\in F^{p+1}N^n$ with $dw=dz$. Then
   $z-w$ is a cycle in $F^pN$, hence $z-w=dv$ for some $v\in F^pN^{n-1}$. Thus the original graded
   cycle is a boundary. Strict surjectivity of $q$ gives a degreewise exact sequence
   $0\to\operatorname{gr}^pN\to\operatorname{gr}^pQ\to\operatorname{gr}^pK\to0$. For the kernel
   assertion, if $x\in F^pQ$ has $qx\in F^{p+1}K$, lift $qx$ to $y\in F^{p+1}Q$ and replace $x$ by
   $x-y\in F^pN$. Finally a degreewise surjective chain map $t:V\to W$ with acyclic kernel $J$ is
   a quasi-isomorphism. For $w\in Z^nW$ lift $w$ to $v\in V^n$. Then $dv\in Z^{n+1}J$, so $dv=du$
   for $u\in J^n$; $v-u$ is a cycle mapping to $w$. If $v\in Z^nV$ and $tv=dw$ with $w\in
   W^{n-1}$, lift $w$ to $y\in V^{n-1}$. Now $v-dy\in Z^nJ$, hence $v-dy=dz$ for $z\in J^{n-1}$
   and $v=d(y+z)$. These are surjectivity and injectivity on cohomology. Apply this chase to the
   displayed graded sequence. Each graded module of $Q^n$ is projective by step 1, so $Q$ has
   every claimed replacement property.
   Dependencies: def-weil-abstract-derived-category, def-sp-filtered-complex-subquotients.
4. For the comparison with unbounded targets, first let $E$ be any globally finite filtered
   complex whose graded complexes are acyclic. Every $F^pE$ is acyclic. To see this without
   assuming that cycles commute with grading, take an actual cycle $z\in F^pE^n$. Acyclicity of
   $\operatorname{gr}^pE$ gives $y_p\in F^pE^{n-1}$ with $z-dy_p\in F^{p+1}E^n$. This residual
   element is still a cycle. Repeat at $p+1$, then at $p+2$, until $F^bE=0$; summing the finitely
   many primitives gives $z=d(\sum y_i)$ inside $F^pE$. For $p<a$ use $F^pE=E=F^aE$, and for $p\ge
   b$ there is nothing to prove. In particular, if $Z^nE=\ker(d:E^n\to E^{n+1})$ has its induced
   filtration, $d:E^{n-1}\to Z^nE$ is a strict filtered surjection. This is a finite filtration
   argument, with no hypothesis on the cochain support of $E$.
   Dependencies: def-sp-filtration, def-sp-filtered-complex-subquotients,
   def-weil-abstract-derived-category.
5. Let $Q$ be bounded above with projective graded modules, and let $u:Q\to E$ be a filtered chain
   map into such a graded-acyclic $E$. Construct a filtered null homotopy $h^n:Q^n\to E^{n-1}$
   downwards from the top cochain degree of $Q$. Set $h^n=0$ above that degree. Suppose the
   homotopy equations hold in all degrees above $n$ and put $r^n=u^n-h^{n+1}d_Q^n$. This has image
   in $Z^nE$, since $$d_Er^n=u^{n+1}d_Q^n-d_Eh^{n+1}d_Q^n=h^{n+2}d_Q^{n+1}d_Q^n=0.$$ It preserves
   every filtration step. By the module-level lifting of step 1 and the strict surjection
   $d:E^{n-1}\to Z^nE$ of step 4, choose a filtered lift $h^n$ of $r^n$. Then
   $u^n=d_Eh^n+h^{n+1}d_Q^n$. This proves the induction and constructs a null homotopy in every
   degree. Each degree is reached after finitely many steps, although $Q$ need not be bounded
   below. The same conclusion applies to any cochain shift of a graded-acyclic $E$, using the
   unchanged filtration indices and the usual signed shift differential.
   Dependencies: def-weil-pbc-projective-module, def-sp-filtration,
   def-weil-abstract-derived-category, def-kun-finite-filtered-module-homotopy.
6. Let $s:X\to Y$ be a filtered quasi-isomorphism, with $X,Y$ arbitrary, and fix a bounded-above
   filtered projective $Q$. If $X,Y$ have filtration bounds $a_X,b_X$ and $a_Y,b_Y$, their direct
   sum has bounds $\min(a_X,a_Y),\max(b_X,b_Y)$. Give $C=\operatorname{Cone}(s)$ the direct-sum
   filtration, so $C^n=Y^n\oplus X^{n+1}$ and $d_C(y,x)=(d_Yy+s x,-d_Xx)$. The graded quotient of
   this direct sum is the direct sum of the graded quotients, with the same displayed
   differential, hence $\operatorname{gr}^pC=\operatorname{Cone}(\operatorname{gr}^ps)$. The
   ordinary cone criterion makes each graded complex acyclic, so step 5 applies to $C$ and
   $C[-1]$. For surjectivity of $s_*:\operatorname{Hom}_{KF}(Q,X)\to\operatorname{Hom}_{KF}(Q,Y)$,
   take $f:Q\to Y$ and null-homotope $(f,0):Q\to C$. Write this homotopy as $(a,b)$, where
   $a^n:Q^n\to Y^{n-1}$ and $b^n:Q^n\to X^n$. Its equations say $d_Xb=bd_Q$ and $f-sb=d_Ya+ad_Q$.
   Thus $b$ is a filtered chain map with $s_*[b]=[f]$. For injectivity suppose $g:Q\to X$ and
   $sg=d_Ya+ad_Q$. In $C[-1]^n=Y^{n-1}\oplus X^n$ the differential is
   $(y,x)\mapsto(-d_Yy-sx,d_Xx)$, and $(-a,g):Q\to C[-1]$ is a filtered chain map. A null homotopy
   of it has second component $e^n:Q^n\to X^{n-1}$ satisfying $g=d_Xe+ed_Q$. Thus $[g]=0$.
   Applying this to the difference of two maps proves injectivity. Consequently
   $\operatorname{Hom}_{KF}(Q,-)$ inverts every filtered quasi-isomorphism, including ones between
   unbounded complexes.
   Dependencies: def-weil-abstract-derived-category, def-sp-filtration,
   def-sp-filtered-complex-subquotients, lem-pur-quasi-iso-cone-acyclic,
   def-kun-finite-filtered-module-homotopy.
7. Here is the categorical passage to the localization, with no boundedness assumption hidden in a
   fraction theorem. Put $\mathcal C=KF(A)$, $L:\mathcal C\to DF(A)$, and
   $H=\operatorname{Hom}_{\mathcal C}(Q,-)$, a functor to sets in a common sufficiently large
   universe. Step 6 says that $H$ inverts all denominators. By the localization universal property
   (1) there are $\overline H:DF(A)\to\mathbf{Set}$ and $\phi:\overline H L\cong H$. Put
   $B=\operatorname{Hom}_{DF(A)}(LQ,-)$; its restriction also inverts denominators. The natural
   map $\tau:H\to BL$, $f\mapsto Lf$, lifts by part (2) of the same cited statement to
   $\eta:\overline H\to B$, with $\eta_{LE}=\tau_E\phi_E$. Define $$e=\phi_Q^{-1}(1_Q),\qquad
   r_E(\alpha)=\phi_E\bigl(\overline H(\alpha)(e)\bigr)\quad(\alpha:LQ\to LE).$$ Naturality of
   $\phi$ gives $r_E(Lf)=f$. Naturality of $\eta$ gives $$L(r_E(\alpha))=\eta_{LE}(\overline
   H(\alpha)e)=B(\alpha)(\eta_{LQ}(e))=\alpha,$$ since $\eta_{LQ}(e)=L(1_Q)=1_{LQ}$. Thus $r_E$
   and $f\mapsto Lf$ are inverse bijections, exactly the claimed comparison with unrestricted
   targets. The identical argument applies to the localization of the bounded-above subcategory,
   because step 6 applies in particular to all its denominators. This argument uses only functor
   and natural-transformation factorization, not the abelian-category theorem about ordinary
   K-projective complexes.
   Dependencies: def-kun-finite-filtered-module-homotopy,
   lem-weil-pbc-localization-universal-property.
8. Let $\mathcal P^-$ be the full subcategory of $KF^-(A)$ on the bounded-above filtered complexes
   with projective graded modules. Step 7, applied in the bounded-above homotopy category, says
   its composite functor to $DF^-(A)$ is fully faithful. Steps 2 and 3 show every object of
   $DF^-(A)$ is isomorphic to the image of an object of $\mathcal P^-$ via a filtered
   quasi-isomorphism. Explicitly, choose for every bounded-above $K$ one replacement $q_K:Q_K\to
   K$. For a localized morphism $\alpha:K\to K'$, define its inverse-equivalence image to be the
   unique homotopy class $Q_K\to Q_{K'}$ whose localized image is $L(q_{K'})^{-1}\alpha L(q_K)$,
   using the bijection in step 7. Uniqueness verifies identities and composition; the $L(q_K)$
   give the counit isomorphisms. For a projective object the same bijection lifts these
   isomorphisms and their inverses, giving the unit. This exhibits the asserted equivalence and
   specifies that it is induced by the localization functor.
   Dependencies: def-kun-finite-filtered-module-homotopy,
   lem-weil-pbc-localization-universal-property.
9. Finally run the entire argument in the category of two-step filtrations with the fixed bounds
   $a=0,b=2$. The free cover of step 1 has weights only $0,1$, so the construction in step 2 stays
   in two-step filtrations and produces $Q'\subset Q$ with projective graded modules $Q'$ and
   $Q/Q'$. Kernels, cycles, direct sums, cones and cochain shifts used in steps 3--6 retain these
   same two filtration indices. Thus testing the two graded complexes is precisely the test used
   in every argument, and step 7 applies to the separate two-step localization as well. A map or
   homotopy between two such embedded complexes preserves all filtration indices exactly when it
   preserves the one specified subcomplex. Hence its homotopy-category Hom set agrees with the
   corresponding Hom set in $KF(A)$. For a bounded-above two-step projective $Q$ and an arbitrary
   two-step $E$, the canonical Hom bijections of step 7 for the two localizations both send a
   chain-map class $[f]$ to its localization. Inclusion preserves denominators, hence induces the
   functor between the two localizations; its Hom map intertwines those two bijections and is
   therefore bijective. This proves every two-step assertion, including unbounded targets, without
   replacing filtration-preserving maps by strict maps.
   Dependencies: def-sp-filtration, def-sp-filtered-complex-subquotients,
   def-kun-finite-filtered-module-homotopy, lem-weil-pbc-localization-universal-property. -/
theorem filteredProjectiveComparison :
    Functor.IsEquivalence (boundedProjectiveLocalizationFunctor R) ∧
      (∀ (K : FiniteFilteredModuleHomotopy R), IsBoundedAbove R K →
        ∃ (Q : FiniteFilteredModuleHomotopy R),
          IsBoundedAbove R Q ∧ IsGradedProjective R Q ∧
            ∃ f : Q ⟶ K, finiteFilteredModuleQuasiIso R f) ∧
      (∀ (Q E : FiniteFilteredModuleHomotopy R),
        IsBoundedAbove R Q → IsGradedProjective R Q →
          Function.Bijective (fun f : Q ⟶ E ↦
            (MorphismProperty.Q (finiteFilteredModuleQuasiIso R)).map f)) ∧
      Functor.IsEquivalence (twoStepBoundedProjectiveLocalizationFunctor R) ∧
      (∀ (K : TwoStepModuleHomotopy R), IsTwoStepBoundedAbove R K →
        ∃ (Q : TwoStepModuleHomotopy R),
          IsTwoStepBoundedAbove R Q ∧ IsTwoStepGradedProjective R Q ∧
            ∃ f : Q ⟶ K, twoStepModuleQuasiIso R f) ∧
      (∀ (Q E : TwoStepModuleHomotopy R),
        IsTwoStepBoundedAbove R Q → IsTwoStepGradedProjective R Q →
          Function.Bijective (fun f : Q ⟶ E ↦
            (MorphismProperty.Q (twoStepModuleQuasiIso R)).map f)) ∧
      (∀ (Q E : TwoStepModuleHomotopy R),
        IsTwoStepBoundedAbove R Q → IsTwoStepGradedProjective R Q →
          Function.Bijective (fun f :
              (MorphismProperty.Q (twoStepModuleQuasiIso R)).obj Q ⟶
                (MorphismProperty.Q (twoStepModuleQuasiIso R)).obj E ↦
            (twoStepToFilteredDerived R).map f)) := by
  sorry

end CochainComplex
