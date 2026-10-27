/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.PrimeToEllAlterationTopology
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Sheaf.CategoryTheory.Sites.GrothendieckTopos
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme

/-!
# Cover calculus for prime-to-ell alterations

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II,
1.2.5--1.2.8, 2.2.4 and 2.3.1--2.3.2, printed pp. 25--28
(blueprint: lem-per-alteration-cover-calculus).

The dominant integral change of base is the generator-tree expansion of II 1.2.5--1.2.8,
retaining dominating components; flatness is not assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u w w' w''

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PrimeToEllAlteration

/-- Cover calculus in `alt/S`. Source: ILO II 1.2.5--1.2.8, 2.2.4, 2.3.1--2.3.2
(blueprint: lem-per-alteration-cover-calculus).

Proof plan, with the dependency nodes of each step:

1. By the definition of $\operatorname{alt}/S$, its objects have exactly the reducedness, finite-
type and generic-point properties asserted. Each object is Noetherian by finite-type preservation
of Noetherianity. Apply the generic-fibre finiteness criterion: its fibres over generic points of
$S$ are finite schemes. For an $S$-map $X\to Y$ of objects, the image of a generic point of $X$
lies in such a finite fibre of $Y$, and any generic generization of that image still lies in this
zero-dimensional fibre, hence equals it. Thus the image is a generic point of $Y$; its residue
field is an intermediate field of the finite extension belonging to $X$. Thus every arrow is
maximally dominant and has finite generic residue extensions. On affine charts, generators of the
source algebra over the base also generate it over the intermediate target algebra. The source is
Noetherian, so preimages of affine opens are quasi-compact. Hence these arrows are of finite type
as well.
Uses: def-per-prime-to-ell-alteration-topology, lem-weil-pbc-finite-type-over-noetherian, lem-per-
generic-fibre-finiteness-criterion.

2. For arrows $X\to T\leftarrow Y$ of $\operatorname{alt}/S$, form the usual scheme fibre product
$P=X\times_TY$. It is of finite type over $S$: the arrows to $T$ are of finite type by Step 1, and
finite type is stable under base change and composition. Put $Q=P_{\mathrm{md}}$ relative to $S$.
The dominant-closure universal property factors every compatible pair of maps from an object of
$\operatorname{alt}/S$ uniquely through $Q$; thus it gives the required fibre-product universal
property. The generic fibre $P_s$ is a fibre product of finite schemes over a finite scheme, so is
finite: on affine fibres its coordinate algebra is the tensor product of two finite-dimensional
algebras, spanned by the finitely many tensors of basis elements. Its reduction $Q_s$ is finite
too. Consequently $Q$ has finite generic residue extensions and is an object of
$\operatorname{alt}/S$. By Step 1, a component of $P$ dominates a component of $S$ exactly when it
dominates a component of the common target $T$; this also proves the stated description relative
to that base.
Uses: def-pc-fibre-product, lem-per-dominant-part-coreflection, lem-sfb-finite-type-composition-
base-change.

3. Check pullback on each of the two generating types. For an etale $\ell'$-decomposed family
$U_i\to X$ and $Y\to X$ in $\operatorname{alt}/S$, the etale dominant-closure comparison
identifies its categorical pullback with the ordinary etale pullback $U_i\times_XY$. Given $y\in
Y$ over $x$, choose a good point $u\in U_i$ over $x$ and apply the residue-degree lemma to
$\kappa(u)/\kappa(x)$ and $\kappa(y)/\kappa(x)$. It supplies a point over $y$ with degree prime to
$\ell$, so this pullback is again a generator. For a proper surjective maximally $\ell'$-finite
map $U\to X$, its ordinary pullback to $Y$ is proper and surjective; dominant reduction preserves
both properties. At each generic point $y$ of $Y$, its image is generic in $X$ by Step 1. Apply
the same residue-degree lemma there. Its good generic-fibre point survives dominant reduction, so
the resulting map is maximally $\ell'$-finite. Thus both generating types are stable under the
categorical pullbacks of Step 2.
Uses: def-per-prime-to-ell-alteration-topology, lem-per-dominant-part-coreflection, lem-per-prime-
to-ell-residue-base-change, lem-weil-pbc-etale-covering-base-change, lem-weil-pbc-proper-base-
change, lem-weil-pbc-surjective-base-change.

4. Every etale generator contains a finite etale $\ell'$-decomposed subfamily by finite
extraction; its target is Noetherian by Step 1. Proper generators already have one member. Take as
a precoverage $K$ the families of leaf composites of finite rooted trees, allowing a singleton
isomorphism or a finite generating family at each vertex (and the empty generating family over the
empty scheme). Grafting trees gives composition stability. Pull back a tree one vertex at a time
using Step 3; induction on its finite height gives a finite tree of generators whose leaves are
the pullbacks of its original leaves. Hence $K$ is stable under base change, and Step 2 supplies
all its required pullbacks. A finite tree has finitely many leaves, so every member of $K$ is
finite. This construction closes the generators under composition; it does not assert that the two
raw generating types themselves are composition-stable.
Uses: lem-per-prime-to-ell-decomposed-etale-finite-subcover, def-per-prime-to-ell-alteration-
topology.

5. The topology generated by $K$ equals the topology in the statement. Indeed each original etale
generator contains one of the finite generators used in $K$, while every tree in $K$ is covering
for the original topology by repeated local character; proper generators occur in $K$ directly.
These give both inclusions by the defining minimality of the generated topology. Apply the
generated-precoverage membership theorem to $K$, using its composition stability, base-change
stability, pullbacks and singleton isomorphisms from Step 4. Every covering sieve contains the
presieve of some tree in $K$, which is a finite covering family. In particular every covering
family has a finite tree refinement: its generated sieve contains the leaves of such a tree, and
membership in that sieve supplies a factorization of each leaf through a member of the original
family.
Uses: def-per-prime-to-ell-alteration-topology, def-weil-pbc-topos, lem-per-generated-precoverage-
covering-sieve.

6. For completeness, apply the sieve axioms directly to arbitrary covering families. If $A_i\to X$
covers and for each $i$ the family $B_{ij}\to A_i$ covers, let $R$ be the sieve generated by the
composites. Its pullback along $A_i\to X$ contains the covering sieve generated by the $B_{ij}$,
and is therefore covering. Local character makes $R$ covering. This proves composition, including
refinements by covering families. A coarser family through which a covering family factors is
covering because its sieve contains a covering sieve. For pullbacks, a map belongs to the pullback
of the sieve generated by $A_i\to X$ exactly when it factors through one of the categorical fibre
products $A_i\times_XY$; the equivalence follows by pairing the factorization with its given map
to $Y$. The pullback-sieve axiom therefore proves stability of every covering family. Composite
finite families remain finite because their indices form a finite union of finite sets.
Uses: def-weil-pbc-topos, def-per-prime-to-ell-alteration-topology, def-pc-fibre-product.

7. Now let $a:S'\to S$ be dominant of finite type between integral Noetherian schemes. Define
$F(X)=(X\times_SS')_{\mathrm{md}}$ relative to $S'$. Finite-type base change and composition make
all schemes used here finite type. At the generic point of $S'$, the fibre is the reduction of the
scalar extension of the finite generic fibre of $X$, so it is finite. Thus $F(X)$ is in
$\operatorname{alt}/S'$. Functoriality of dominant closure gives $F$ on arrows. To compare
successive products and dominant reductions, take a reduced finite-type scheme $T$ maximally
dominant over $S'$. Its composite to $S$ is maximally dominant because $a$ is dominant and both
bases are integral. Every map $T\to X\times_SS'$ therefore factors uniquely through the dominant
part of any intermediate finite-type $S$-scheme through which it is expressed. Apply this
factorization in both orders to the ordinary fibre-product cones. Uniqueness identifies their
dominant reductions, compatibly with projections. Hence $F$ preserves the categorical fibre
products needed for tree pullbacks. This argument uses dominance, not flatness.
Uses: lem-per-dominant-part-coreflection, lem-sfb-finite-type-composition-base-change, def-pc-
fibre-product.

8. The functor $F$ sends each generator to a generator. For etale maps, the comparison
$F(U)=U\times_XF(X)$ is the etale dominant-closure comparison over $S'$. Given a point of $F(X)$,
apply the residue-degree lemma to its residue field and a good point in $U$ over its image in $X$.
For a proper generator, ordinary base change is proper and surjective and dominant reduction
preserves these properties. A generic point of $F(X)$ maps into the generic fibre of $X$ over $S$,
whose points are generic in $X$ by Step 1. The residue-degree lemma again supplies a good point at
that generic point; dominant reduction retains it. Therefore proper maximally $\ell'$-finite
surjections remain such. A finite generator tree refinement from Step 5 maps under $F$ to a tree
of generators: its factorization arrows remain factorization arrows by functoriality. Its leaves
give a covering family refining the images of the original covering family. Coarsening as in Step
6 proves the claimed dominant base-change stability.
Uses: def-per-prime-to-ell-alteration-topology, lem-per-dominant-part-coreflection, lem-per-prime-
to-ell-residue-base-change, lem-weil-pbc-etale-covering-base-change, lem-weil-pbc-proper-base-
change, lem-weil-pbc-surjective-base-change.

9. For integral schemes the unique generic residue-field extension of a proper surjective
generically finite morphism has its generic degree. If this is prime to $\ell$, the morphism is
precisely a proper surjective maximally $\ell'$-finite generator. A proper birational morphism has
generic degree $1$, so is covered by the same case. These assertions concern morphisms between
objects of the relevant alteration category; in particular for such a map to an integral target
$X$, one may use $\operatorname{alt}/X$.
Uses: def-per-prime-to-ell-alteration-topology.

10. For a finite affine open cover $X=\bigcup_iU_i$, the inclusions are etale, and a point lying
in $U_i$ lifts with unchanged residue field, of degree $1$. Thus this is an etale
$\ell'$-decomposed generator. Each open is reduced and has the required generic-point property
inherited from $X$; a quasi-compact open immersion is of finite type, so these affine opens are
objects of $\operatorname{alt}/S$. This proves the open-cover assertion also for the empty object,
with the empty family.
Uses: def-per-prime-to-ell-alteration-topology, lem-weil-pbc-open-immersion-etale, lem-weil-pbc-
qc-open-immersion-finite-type.

11. Finally let $X$ be a reduced object and write its finitely many reduced irreducible components
as $C_j$. Their reduced closed scheme structures exist; their inclusions are finite, hence proper.
Form $C=\coprod_j C_j$. On an affine $\operatorname{Spec}A\subset X$, this map is given by
$A\to\prod_j A/\mathfrak p_j$ for the component primes meeting that affine. This algebra is a
finite $A$-module, so $C\to X$ is finite and hence proper. It is surjective, and at each generic
point has a lift with identical residue field. Thus $C\to X$ is a singleton alteration generator.
The scheme $C$ and each $C_j$ are reduced finite-type objects with the asserted generic points.
The component summands form a finite open cover of $C$, so by Step 10 their composites $C_j\to X$
cover by Step 6. Equivalently, the pullback to $C$ of the sieve generated by the component
inclusions contains that open cover, and local character gives the desired component-family
covering of $X$. If $X$ is empty, use the empty cover directly.
Uses: lem-weil-pbc-noetherian-finite-components, lem-weil-pbc-reduced-induced-closed-subscheme,
lem-weil-pbc-closed-immersion-finite, lem-weil-pbc-finite-proper, lem-weil-pbc-scheme-coproduct-
family, def-per-prime-to-ell-alteration-topology.
-/
theorem alteration_cover_calculus (S : Scheme.{u}) [IsNoetherian S]
    (ell : ℕ) [Fact ell.Prime] :
    (∀ {T : Alt S} {I : Type w} [Finite I] {J : I → Type w'} [∀ i, Finite (J i)]
      (U : I → Alt S) (f : ∀ i, U i ⟶ T)
      (V : ∀ i, J i → Alt S) (g : ∀ i j, V i j ⟶ U i),
      IsCoveringFamily ell U f → (∀ i, IsCoveringFamily ell (V i) (g i)) →
        IsCoveringFamily ell (fun ij : Sigma J ↦ V ij.1 ij.2)
          (fun ij ↦ g ij.1 ij.2 ≫ f ij.1)) ∧
    (∀ {T : Alt S} {I : Type w} {J : I → Type w'} {K : Type w''}
      (U : I → Alt S) (f : ∀ i, U i ⟶ T)
      (V : ∀ i, J i → Alt S) (g : ∀ i j, V i j ⟶ U i)
      (W : K → Alt S) (h : ∀ k, W k ⟶ T),
      IsCoveringFamily ell U f → (∀ i, IsCoveringFamily ell (V i) (g i)) →
        Refines (fun ij : Sigma J ↦ V ij.1 ij.2)
          (fun ij ↦ g ij.1 ij.2 ≫ f ij.1) W h → IsCoveringFamily ell W h) ∧
    (∀ (T : Alt S) (R : Sieve T), R ∈ topology S ell T →
      ∃ (n : ℕ) (U : Fin n → Alt S) (f : ∀ i, U i ⟶ T),
        IsCoveringFamily ell U f ∧ ∀ i, R (f i)) ∧
    (∀ {X Y T : Alt S} (f : X ⟶ T) (g : Y ⟶ T),
      ∃ (P : Alt S) (p : P ⟶ X) (q : P ⟶ Y)
        (j : P.obj.left ⟶ pullback f.hom.left g.hom.left),
        IsPullback p q f g ∧ IsClosedImmersion j ∧
        j ≫ pullback.fst f.hom.left g.hom.left = p.hom.left ∧
        j ≫ pullback.snd f.hom.left g.hom.left = q.hom.left ∧
        Set.range j = {z | ∃ c : Set (pullback f.hom.left g.hom.left : Scheme.{u}),
          c ∈ irreducibleComponents (pullback f.hom.left g.hom.left : Scheme.{u}) ∧
          z ∈ c ∧ closure ((pullback.fst f.hom.left g.hom.left ≫ f.hom.left) '' c) ∈
            irreducibleComponents T.obj.left}) ∧
    (∀ {T Y : Alt S} {I : Type w} (U : I → Alt S) (f : ∀ i, U i ⟶ T)
      (g : Y ⟶ T) (P : I → Alt S) (p : ∀ i, P i ⟶ U i) (q : ∀ i, P i ⟶ Y),
      IsCoveringFamily ell U f → (∀ i, IsPullback (p i) (q i) (f i) g) →
        IsCoveringFamily ell P q) ∧
    (∀ (S' : Scheme.{u}) [IsIntegral S] [IsIntegral S'] [IsNoetherian S']
      (a : S' ⟶ S) [IsDominant a] [LocallyOfFiniteType a] [QuasiCompact a],
      ∃ (F : Alt S ⥤ Alt S')
        (j : ∀ X : Alt S, (F.obj X).obj.left ⟶ pullback X.obj.hom a),
        (∀ X, IsClosedImmersion (j X)) ∧
        (∀ X, Set.range (j X) = {z | ∃ c : Set (pullback X.obj.hom a : Scheme.{u}),
          c ∈ irreducibleComponents (pullback X.obj.hom a : Scheme.{u}) ∧ z ∈ c ∧
            closure (pullback.snd X.obj.hom a '' c) = Set.univ}) ∧
        (∀ X, j X ≫ pullback.snd X.obj.hom a = (F.obj X).obj.hom) ∧
        (∀ {X Y : Alt S} (f : X ⟶ Y),
          (F.map f).hom.left ≫ j Y ≫ pullback.fst Y.obj.hom a =
            j X ≫ pullback.fst X.obj.hom a ≫ f.hom.left) ∧
        (∀ {T : Alt S} {I : Type w} (U : I → Alt S) (f : ∀ i, U i ⟶ T),
          IsCoveringFamily ell U f →
            IsCoveringFamily ell (fun i ↦ F.obj (U i)) (fun i ↦ F.map (f i)))) ∧
    (∀ {X T : Alt S} [IsIntegral X.obj.left] [IsIntegral T.obj.left]
      (f : X ⟶ T) [IsProper f.hom.left] [Surjective f.hom.left],
      (∀ x : X.obj.left, closure ({x} : Set X.obj.left) ∈
        irreducibleComponents X.obj.left →
          (f.hom.left.residueFieldMap x).hom.Finite ∧
            Nat.Coprime (f.hom.left.residueDegree x) ell) →
      IsCoveringFamily ell (fun _ : Fin 1 ↦ X) (fun _ ↦ f)) ∧
    (∀ {X T : Alt S} [IsIntegral X.obj.left] [IsIntegral T.obj.left]
      (f : X ⟶ T) [IsProper f.hom.left],
      (∃ V : T.obj.left.Opens, Dense (V : Set T.obj.left) ∧ IsIso (f.hom.left ∣_ V)) →
        IsCoveringFamily ell (fun _ : Fin 1 ↦ X) (fun _ ↦ f)) ∧
    (∀ {T : Alt S} {I : Type w} [Finite I] (U : I → Alt S) (f : ∀ i, U i ⟶ T),
      (∀ i, IsAffine (U i).obj.left) → (∀ i, IsOpenImmersion (f i).hom.left) →
      (∀ t : T.obj.left, ∃ (i : I) (x : (U i).obj.left), (f i).hom.left x = t) →
        IsCoveringFamily ell U f) ∧
    (∀ T : Alt S, ∃ (n : ℕ) (U : Fin n → Alt S) (f : ∀ i, U i ⟶ T)
      (e : Fin n ≃ {c : Set T.obj.left // c ∈ irreducibleComponents T.obj.left}),
      (∀ i, IsClosedImmersion (f i).hom.left) ∧
      (∀ i, Set.range (f i).hom.left = (e i).1) ∧ IsCoveringFamily ell U f) ∧
    (∀ T : Alt S, IsReduced T.obj.left ∧ LocallyOfFiniteType T.obj.hom ∧
      QuasiCompact T.obj.hom ∧
      ∀ t : T.obj.left, closure ({t} : Set T.obj.left) ∈ irreducibleComponents T.obj.left →
        closure ({T.obj.hom t} : Set S) ∈ irreducibleComponents S ∧
          (T.obj.hom.residueFieldMap t).hom.Finite) := by
  sorry

end AlgebraicGeometry.PrimeToEllAlteration
