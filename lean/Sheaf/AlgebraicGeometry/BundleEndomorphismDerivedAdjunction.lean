/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The SHEAF contributors
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalDerivedHom
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Sheaf.AlgebraicGeometry.CoherentFiniteType
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.DerivedCategory.RightDerivedFromAdaptedComplexes
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom
import Sheaf.Algebra.Homology.KInjectiveHomComplex
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated

/-! # Unbounded tensor and global Hom for a vector bundle

Source: Stacks Project, dga.tex, Tags 09LX and 09LY; perfect.tex, Tag 09M3;
sites-cohomology.tex, Tags 0A96 and 0B6E
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction).

Right B-modules are left modules over Bᵐᵒᵖ, for B = End E with composition multiplication.
The ordinary balanced tensor is Mathlib's uniquely characterized left adjoint to
`preadditiveCoyonedaObj E`. The latter is the global Hom functor with precomposition action.
Its unbounded right derived functor is the existing K-injective construction.

The A-scheme structure is encoded by its equivalent structural map A → Γ(X, O_X).
The A-linear structure is existentially supplied and specified on every sheaf morphism
by multiplication with the image of A; it is not an arbitrary coefficient action.

## Main definitions and statement

* `tensor`, `hom`, `derivedHom`, `qcHom`: the shared tensor and Hom constructions.
* `scalarsCompatible`: the structural coefficient action on every sheaf morphism.
* `globalHom`: the shared global derived Hom, restricted to the base ring.
* `adjunctionStatement`: derived existence, adjunction, resolution model and comparisons.
* `tensor_derived_adjunction`: the complete vector-bundle assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u a w wB wA wΓ
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped ModuleCat.Algebra

namespace AlgebraicGeometry
namespace BundleEndomorphism

variable (X : Scheme.{u})

/-- The existing category of O_X-modules, without changing its category instance. Source: Stacks,
Tag 03DA
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
abbrev Modules := SheafOfModules.{u} (moduleRings X.toRingedSpace)
/-- The ring Γ(X, O_X), evaluated at the whole space. Source: Stacks, Tag 0B6E
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
abbrev Scalars := ((moduleRings X.toRingedSpace).obj.obj (op ⊤))

/-- The ordinary balanced tensor V_E = - ⊗_End(E) E, using Mathlib's left adjoint to global Hom. Its
adjunction uniquely identifies it with the sheaf associated to U ↦ L ⊗_B E(U): the balanced
evaluation formula gives the same representing property. Source: Stacks, Tags 09LV and 09LX
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
noncomputable abbrev tensor (E : Modules X) : ModuleCat.{u} (End E)ᵐᵒᵖ ⥤ Modules X :=
  IsGrothendieckAbelian.tensorObj E

/-- Additivity supplied by the existing ordinary tensor-Hom adjunction. Source: Stacks, Tag 09LW
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
instance tensorAdditive (E : Modules X) : (tensor X E).Additive :=
  (IsGrothendieckAbelian.tensorObjPreadditiveCoyonedaObjAdjunction E).left_adjoint_additive

/-- Global Hom from E, with right End(E)-action f · b = b ≫ f and maps given by postcomposition.
Source: Stacks, Tag 09LY
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
noncomputable abbrev hom (E : Modules X) := preadditiveCoyonedaObj E

variable [HasDerivedCategory.{w} (Modules X)]

/-- E in degree zero in the shared unbounded derived category. Source: Stacks, Tag 09LX
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
noncomputable abbrev single (E : Modules X) : schemeDerivedCategory X :=
  (DerivedCategory.singleFunctor (Modules X) 0).obj E

/-- The unbounded right derived functor of the existing global Hom, constructed on K-injective
complexes with its actual right End(E)-action. Source: Stacks, dga.tex,
lemma-existence-of-derived
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
noncomputable abbrev derivedHom (E : Modules X)
    [HasDerivedCategory.{wB} (ModuleCat.{u} (End E)ᵐᵒᵖ)] :=
  (hom X E).rightDerivedFunctor

/-- The preceding right derived Hom restricted to the full subcategory with quasi-coherent
cohomology. Source: Stacks, Tags 09LY and 09M3
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
noncomputable abbrev qcHom (E : Modules X)
    [HasDerivedCategory.{wB} (ModuleCat.{u} (End E)ᵐᵒᵖ)] :=
  (schemeDerivedQCohProperty X).ι ⋙ derivedHom X E

/-- The structural A-action on every sheaf morphism: multiply locally by the restriction of aX(a).
This fixes the induced central map A → End(E) and hence its opposite-ring map. Source: Stacks,
Tag 09LY, scalar formulas
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
def scalarsCompatible (A : Type a) [CommRing A] (aX : A →+* Scalars X)
    [linearInst : Linear A (Modules X)] : Prop :=
  ∀ (M N : Modules X) (a : A) (f : M ⟶ N),
    a • f = f ≫ @id (N ⟶ N) (Scheme.Modules.smulHom (X := X) N (aX a))

/-- The shared global derived Hom from E[0], followed by restriction from Γ(X,O_X) to A. Source:
Stacks, Tag 0B6E
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
noncomputable def globalHom (A : Type a) [CommRing A] (aX : A →+* Scalars X)
    (E : Modules X) [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wΓ} (ModuleCat.{u} (Scalars X))] :
    schemeDerivedQCohCategory X ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (Functor.const _).obj (op (single X E)) |>.prod' (schemeDerivedQCohProperty X).ι |>.comp
    (schemeGlobalDerivedHom X ⋙ (ModuleCat.restrictScalars aX).mapDerivedCategory)

/-- All clauses of the bundle endomorphism derived adjunction, on the existing unbounded categories.
The left-derived universal property concerns the specified ordinary balanced tensor. Exactness
is expressed on the ambient derived categories, whose full quasi-coherent subcategory has the
induced distinguished triangles. The derived restriction of scalars is used also for the
possibly noncommutative ring End(E). Its underlying functor is exact restriction of scalars. The
final family consists of additive equivalences, natural in K, intertwining the full right
End(E)-action with precomposition for every integer q. K-injectivity is the existing
all-acyclic-sources predicate (equivalently acyclicity of the mapping complex, since it tests
every shift). Source: Stacks, Tags 09LX, 09LY, 09M3, 0A96 and 0B6E
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction). -/
noncomputable def adjunctionStatement (A : Type a) [CommRing A]
    (aX : A →+* Scalars X) (E : Modules X) [linearInst : Linear A (Modules X)]
    [HasDerivedCategory.{wB} (ModuleCat.{u} (End E)ᵐᵒᵖ)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wΓ} (ModuleCat.{u} (Scalars X))] : Prop :=
  ∃ F : DerivedCategory (ModuleCat.{u} (End E)ᵐᵒᵖ) ⥤ schemeDerivedQCohCategory X,
    (∃ eps : DerivedCategory.Qh ⋙ (F ⋙ (schemeDerivedQCohProperty X).ι) ⟶
        (tensor X E).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh,
      (F ⋙ (schemeDerivedQCohProperty X).ι).IsLeftDerivedFunctor eps
        (HomotopyCategory.quasiIso _ (.up ℤ))) ∧
    Nonempty ((F ⋙ (schemeDerivedQCohProperty X).ι).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (End E)ᵐᵒᵖ) 0).obj
        (ModuleCat.of (End E)ᵐᵒᵖ (End E)ᵐᵒᵖ)) ≅ single X E) ∧
    (∃ s : (F ⋙ (schemeDerivedQCohProperty X).ι).CommShift ℤ,
      @Functor.IsTriangulated _ _ _ _ _ _
        (F ⋙ (schemeDerivedQCohProperty X).ι) s _ _ _ _ _ _ _ _) ∧
    (∃ s : (derivedHom X E).CommShift ℤ,
      @Functor.IsTriangulated _ _ _ _ _ _ (derivedHom X E) s _ _ _ _ _ _ _ _) ∧
    F.Linear A ∧ (qcHom X E).Linear A ∧
    (∃ adj : F ⊣ qcHom X E, ∀ (L : DerivedCategory (ModuleCat.{u} (End E)ᵐᵒᵖ))
        (K : schemeDerivedQCohCategory X) (f : F.obj L ⟶ K) (a : A),
      adj.homEquiv L K (a • f) = a • adj.homEquiv L K f) ∧
    Nonempty (qcHom X E ⋙
      (ModuleCat.restrictScalars (algebraMap A (End E)ᵐᵒᵖ)).rightDerivedFunctor ≅
        globalHom X A aX E) ∧
    (∀ (K I : CochainComplex (Modules X) ℤ) (s : K ⟶ I),
      QuasiIso s → I.IsKInjective →
        Nonempty ((derivedHom X E).obj (DerivedCategory.Q.obj K) ≅
          DerivedCategory.Q.obj (((hom X E).mapHomologicalComplex (.up ℤ)).obj I))) ∧
    ∃ e : ∀ (K : schemeDerivedQCohCategory X) (q : ℤ),
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (End E)ᵐᵒᵖ) q).obj
          ((qcHom X E).obj K)) ≃+ (single X E ⟶ K.obj⟦q⟧),
      (∀ (K : schemeDerivedQCohCategory X) (q : ℤ) (b : (End E)ᵐᵒᵖ)
          (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} (End E)ᵐᵒᵖ) q).obj
            ((qcHom X E).obj K)),
        e K q (b • x) = (DerivedCategory.singleFunctor (Modules X) 0).map b.unop ≫
          e K q x) ∧
      ∀ (K L : schemeDerivedQCohCategory X) (f : K ⟶ L) (q : ℤ)
          (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} (End E)ᵐᵒᵖ) q).obj
            ((qcHom X E).obj K)),
        e L q ((DerivedCategory.homologyFunctor (ModuleCat.{u} (End E)ᵐᵒᵖ) q).map
          ((qcHom X E).map f) x) = e K q x ≫ (shiftFunctor _ q).map f.hom

/-- The unbounded tensor-global Hom adjunction for a finite locally free module on a
quasi-compact quasi-separated A-scheme, including coefficients and all integer degrees.
Source: Stacks, Tags 09LX, 09LY, 09M3, 0A96 and 0B6E
(blueprint: lem-sfb-bundle-endomorphism-derived-adjunction).

Proof:
1. Write $T(C)^n=V_E(C^n)$, $d_T=V_E(d_C)$ for a right $B$-module complex $C$, and
$H(J)^n=\operatorname{Hom}_{\mathcal O_X}(E,J^n)$, $d_H(f)=d_Jf$. The right action is $f\cdot
b=f\circ b$: $(f\cdot b_1)\cdot b_2=f\cdot(b_1b_2)$. For a homogeneous map $u:T(C)\to J$, define
$\widehat u(c)(e)=u(c\otimes e)$. Conversely define $\widetilde v(c\otimes e)=v(c)(e)$; this is
balanced since $v(cb)(e)=v(c)(be)$, and extends uniquely through sheafification. These formulas
are inverse and commute with restriction maps. For maps of degree $r$, both carry $d_Ju-(-1)^ru
d_C$ to $d_J\widehat u-(-1)^r\widehat u d_C$. They therefore identify the complexes of global maps
$\operatorname{Hom}_{\mathcal O_X}^{\bullet}(T(C),J)$ and
$\operatorname{Hom}_B^{\bullet}(C,H(J))$, naturally in both arguments. Dependencies:
def-weil-presheaf-modules-sheafification.
2. The additive functors $T$ and $H$ preserve chain homotopies: applying either functor to
$f-g=dh+hd$ gives the same identity. They commute with shifts and cones, because the cone has
terms $J^n\oplus C^{n+1}$ and differential matrix
$\left(\begin{smallmatrix}d_J&f\\0&-d_C\end{smallmatrix}\right)$, and both functors preserve
finite direct sums and that matrix. Thus they induce exact functors on homotopy categories, and
also after exact localization in their targets. Taking degree-zero cycles modulo boundaries in
step 1 gives the ordinary homotopy-category tensor--Hom adjunction. Dependencies:
lem-pur-homotopy-category-triangulated.
3. Regard $B$ as the dg category with one object and endomorphism complex $B[0]$. The semi-free
replacement theorem gives a quasi-isomorphism $P\to C$ for every unbounded right $B$-complex. Its
semi-free source is homotopically projective, hence K-projective: acyclicity of its Hom complex
implies null homotopy of every map to an acyclic complex. If $s:P\to P'$ is a quasi-isomorphism
between such sources, its inverse in the derived category lifts to $t:P'\to P$ by the K-projective
Hom bijection. Injectivity of that bijection, first with source $P$ and then with source $P'$,
gives $ts=1$ and $st=1$ in the homotopy category. Consequently $T(s)$ is a homotopy equivalence.
Apply the left-derived existence criterion to the exact functor $Q_XT$ of step 2 and this
semi-free class. It supplies an everywhere defined exact left derived functor $F_E$, with
$F_E(C)=Q_XT(P)$. The complex $B[0]$ itself is semi-free and $T(B[0])\cong E[0]$ by $b\otimes
e\mapsto b(e)$, inverse $e\mapsto1\otimes e$. Thus $F_E(B)\simeq E$. Dependencies:
lem-coef-dg-module-semi-free-replacement, lem-coef-dg-semi-free-homotopically-projective,
lem-coef-kprojective-derived-hom-bijection, lem-pur-left-derived-from-kflat-class.
4. The split graded filtration of a semi-free $P$ identifies each $P^n$ with a direct sum of
copies of $B$: choose the graded splittings, so the union is the direct sum of successive free
graded quotients. Hence $T(P)^n$ is the corresponding sheaf coproduct of copies of $E$, by
$b\otimes e\mapsto b(e)$ on each summand. The bundle $E$ is quasi-coherent by its local
finite-free description. Coproduct closure makes every $T(P)^n$ quasi-coherent. Kernel closure
gives $Z^n=\ker(d^n)$ quasi-coherent; $d^{n-1}$ factors through $Z^n$ since $d^nd^{n-1}=0$.
Cokernel closure applied to $T(P)^{n-1}\to Z^n$ gives $H^n(T(P))$ quasi-coherent. This proves
$F_E(C)\in D_{\mathrm{QCoh}}(\mathcal O_X)$ for arbitrary $C$, with no boundedness assertion on
$P$. Dependencies: lem-coef-dg-module-semi-free-replacement, pqf-def-coherent,
lem-weil-pbc-quasi-coherent-module-coproduct-closure, lem-weil-pbc-quasi-coherent-module-kernel,
lem-weil-pbc-quasi-coherent-module-cokernel-closure.
5. Use the small Zariski site of $X$, enlarging the module universe if necessary. The ringed-site
resolution theorem gives $K\to I$ with $I$ K-injective for every unbounded complex of $\mathcal
O_X$-modules. A quasi-isomorphism $s:I\to I'$ between K-injectives is a homotopy equivalence: its
derived inverse lifts to $t:I'\to I$ by the K-injective Hom bijection with target $I$, and
injectivity with targets $I,I'$ gives the two inverse identities. The additive functor $H$
preserves this homotopy equivalence. The right-derived existence criterion, applied to $Q_BH$ and
the class of K-injectives, therefore produces a functor $G_E:D(\mathcal O_X)\to
D(\operatorname{Mod}\!\text{-}B)$ computed by $H(I)$. This is a functor with its actual right
$B$-action, because every map, differential, and homotopy used by $H$ commutes with precomposition
by $B$. Shifts and cones of K-injectives are K-injective: mapping an acyclic complex into them
gives shifts or cones of acyclic Hom complexes. Thus a triangle between K-injective
representatives is represented by its actual cone; step 2 shows that $H$ carries it to a cone
triangle. Consequently $G_E$ is exact. Restrict this functor to $D_{\mathrm{QCoh}}(\mathcal O_X)$.
Dependencies: prop-pur-kinjective-resolutions-exist, lem-sc-kinjective-quasi-iso-comparison,
lem-sf-right-derived-from-adapted-complexes.
6. For $L\in D(\operatorname{Mod}\!\text{-}B)$ choose semi-free $P\to L$, and for $K\in D(\mathcal
O_X)$ choose $K\to I$ K-injective. The two localization bijections and step 1 give
$$\operatorname{Hom}_{D(\mathcal O_X)}(F_E(L),K)=\operatorname{Hom}_{K(\mathcal
O_X)}(T(P),I) =
\operatorname{Hom}_{K(\operatorname{Mod}\!\text{-}B)}(P,H(I)) =
\operatorname{Hom}_{D(\operatorname{Mod}\!\text{-}B)}(L,G_E(K)).$$
These bijections are natural: each is induced by localization or by the explicit evaluation maps
of step 1; the bijections make the result independent of the chosen comparison maps between
resolutions. Thus $F_E\dashv G_E$ on the ambient categories. By step 4 the left adjoint lands in
the full subcategory $D_{\mathrm{QCoh}}$, so the same Hom bijection restricts to the required
adjunction there. Dependencies: lem-coef-kprojective-derived-hom-bijection,
lem-sc-kinjective-quasi-iso-comparison, def-pc-derived-category.
7. The complex $E[0]$ is K-flat: for any acyclic $N$, its tensor with $E$ restricts on every
trivializing open to a finite direct sum of copies of $N$. The kernel/image computation of
cohomology is local, and a finite direct sum of exact complexes is exact. Thus $N\otimes E$ is
acyclic on $X$, as required by the definition of K-flatness. Dependencies: def-pc-kflat-complex.
8. By the construction of derived internal Hom, $R\mathcal Hom_{\mathcal O_X}(E,K)$ is represented
by $\mathcal Hom^\bullet(E,I)$. Step 7 and the K-flat/K-injective Hom theorem show that this
representing complex is itself K-injective. The definition of global derived Hom therefore
computes $R\Gamma$ on this very complex without any further replacement:
$$R\operatorname{Hom}_X(E,K)\simeq Q_{\Gamma(X,\mathcal O_X)}\Gamma(X,\mathcal
Hom^\bullet(E,I)).$$ Its degree-$n$ module is exactly $\operatorname{Hom}_{\mathcal O_X}(E,I^n)$
and its differential is $f\mapsto d_If$. Restrict scalars along $A\to\Gamma(X,\mathcal O_X)$: this
is the underlying $A$-complex of $H(I)$, since the scalar $a$ acts on $E$ as the endomorphism
defining $A\to B$. This yields the claimed natural isomorphism in $D(A)$, rather than merely an
equality of cohomology groups. The comparison uses the same maps of K-injective representatives,
so is natural in $K$. Dependencies: def-pur-derived-internal-hom,
lem-pur-hom-kflat-into-kinjective, def-pc-global-derived-rhom.
9. A degree-$q$ cocycle of $H(I)$ is a map $f:E\to I^q$ with $d_If=0$, equivalently a chain map
$E[0]\to I[q]$; the sign in the differential of $I[q]$ does not change the cycle condition.
Boundaries are exactly maps null homotopic as such chain maps (multiplying a homotopy by $(-1)^q$
absorbs the shift sign). Hence $H^q(H(I))=\operatorname{Hom}_{K(\mathcal O_X)}(E,I[q])$. The shift
$I[q]$ is K-injective, since mapping into it shifts the Hom complex. The K-injective localization
bijection gives $H^q(G_E(K))\cong\operatorname{Hom}_{D(\mathcal O_X)}(E,K[q])$. Its naturality in
the source sends $f\circ b$ to precomposition by $b$ in the derived category, proving the right
$B$-action clause for every positive, zero, and negative $q$. Dependencies:
lem-sc-kinjective-quasi-iso-comparison.
10. The scalar map $A\to B$ is central, because every $\mathcal O_X$-linear endomorphism commutes
with multiplication by a global scalar. The maps $c\otimes e\mapsto ac\otimes e=c\otimes ae$ and
$f\mapsto af=f\circ(a\operatorname{id}_E)$ make the functors $T,H$ and the evaluation bijection
$A$-linear. These equalities also hold on complexes, homotopy classes, and the resolved Hom groups
in step 6; thus the derived functors and their adjunction are $A$-linear. Exactness of both
derived functors was obtained in steps 3 and 5 from the exact homotopy functors of step 2 and the
derived-functor criteria. By the triangulated-subcategory theorem with $T=X$,
$D_{\mathrm{QCoh}}(\mathcal O_X)$ contains $0$, is stable under shifts and is closed under middle
terms of distinguished triangles of $D(\mathcal O_X)$, so it is a full triangulated subcategory
whose distinguished triangles are the ambient ones with vertices in it. Hence the restriction of
$G_E$ to it is exact, and the left functor, whose values lie in it by step 4, is exact as a
functor into it. The shift compatibility of the adjunction is the degree-$r$ differential identity
in step 1. Dependencies: lem-pc-supported-qcoh-triangulated.
-/
theorem tensor_derived_adjunction (A : Type a) [CommRing A] (aX : A →+* Scalars X)
    [CompactSpace X] [QuasiSeparatedSpace X] (E : Modules X) [E.IsFiniteLocallyFree]
    [HasDerivedCategory.{wB} (ModuleCat.{u} (End E)ᵐᵒᵖ)]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wΓ} (ModuleCat.{u} (Scalars X))] :
    ∃ linearInst : Linear A (Modules X),
      scalarsCompatible X A aX (linearInst := linearInst) ∧
      adjunctionStatement X A aX E (linearInst := linearInst) := by
  sorry

end BundleEndomorphism
end AlgebraicGeometry
