## Worker report

The module defines the statement `AlgebraicGeometry.scheme_derivedInternalHom_adjunction`
for a scheme `X` with the derived category of `O_X`-modules.  It imports
`Sheaf.AlgebraicGeometry.DerivedTensorStructure` (using
`AlgebraicGeometry.schemeDerivedTensorMonoidal`) and
`Sheaf.Algebra.Homology.DerivedInternalHom` (using
`CategoryTheory.derivedInternalHom`).

The theorem has proof `sorry`, as required for stage 2.  Its first existential component
`e` is a family of equivalences between
`K ⟶ RHom(L,M)` and `K ⊗ L ⟶ M`; this renders the node's canonical bijection.
The second component `s` is a family of isomorphisms `K ⊗ L ≅ L ⊗ K`; its displayed
naturality equation renders functoriality in both tensor variables.  The third component
`e'` is the family of bijections with target `L ⊗ K ⟶ M`, and the equation
`e' f = (s K L).inv ≫ e f` renders its construction from symmetry.  The first and final
naturality equations quantify all six objects and the three morphisms `a`, `b`, and `c`;
`a` is contravariant in `K`, `b` is contravariant in `L` through `b.op` in RHom, and `c`
is covariant in `M`.  `X` and the typeclass hypothesis are explicit binders.  The tensor
is the global derived tensor structure, so no alternate tensor is introduced.

The proof docstring records the node's four proof clauses: K-flat and K-injective
representatives; quasi-isomorphism invariance and the total-complex Hom identity; canonical
independence and naturality; and the Koszul-sign tensor symmetry with K-flat invariance.

Dependency declarations used:

* `AlgebraicGeometry.schemeDerivedCategory` from
  `Sheaf.AlgebraicGeometry.DerivedCategory` (via the imported tensor-structure module).
* `AlgebraicGeometry.schemeDerivedTensorMonoidal` from
  `Sheaf.AlgebraicGeometry.DerivedTensorStructure`.
* `CategoryTheory.derivedInternalHom` from
  `Sheaf.Algebra.Homology.DerivedInternalHom`.
* `CochainComplex.IsKFlat`, `CochainComplex.exists_isKFlatResolution`, and the
  `def-pur-derived-internal-hom` declarations are used in the proof docstring and are
  represented by the imported project modules.
* Scheme and site structures are Mathlib's `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Opens.grothendieckTopology`.

Edge cases checked: the quantifiers allow arbitrary derived objects (including zero
objects), and the tensor variables have no finiteness or boundedness assumptions.  The
scheme may be empty.  The morphism quantifiers include identity and zero morphisms, and
`b.op` preserves the contravariant first argument of RHom.  The universe binders `u,w`
match the existing scheme and derived-category declarations.

Searches made: `msearch.py` LeanFinder query “derived internal Hom tensor adjunction on a
scheme natural in all three variables” returned only generic pullback adjunction hits;
Loogle query “CategoryTheory.Adjunction, CategoryTheory.derivedInternalHom” returned zero
hits; LeanSearch for the same natural-language query was unavailable; Mathlib grep for
`derivedInternalHom|tensorHomAdjunction` returned no relevant sheaf-derived declaration.
`rg` over `WeilConjectures/` and `lean/Sheaf/` found the existing concrete
`CategoryTheory.derivedInternalHom` and the generic upstream
`DerivedCategory.tensorHomAdjunctionQhObj`, but neither states this scheme-level theorem.

No `STATEMENT-DISPUTED` flag or node fault.

## Second reading by P1

Read the item node, its Lean file and every statement-dependency record and declaration.
Read Stacks `cohomology.tex`, the section `section-internal-hom` including equation
`equation-internal-hom`, Lemma `lemma-internal-hom` (08DJ) and its proof, and Lemma
`lemma-symmetric-monoidal-derived` (0FPB). The local source text was available in the
Stacks review checkout. The source assumes a ringed space, arbitrary unbounded derived
objects, and no geometric finiteness hypotheses; a scheme supplies the required ringed
space. The item's conclusion selects the Hom-set bijection recovered from the source's
internal-Hom isomorphism; the stronger intermediate object isomorphism is not an extra
conclusion of this node.

Object/hypothesis/conclusion checklist, with the Lean rendering and verdict:

1. Scheme X: `(X : Scheme.{u})`, Mathlib's `AlgebraicGeometry.Scheme` from
   `def-pc-scheme`, extending a locally ringed space with local affine charts. PASS.
   No field, characteristic, Noetherian, separation, quasi-compactness or nonemptiness
   hypothesis is introduced.
2. D(O_X): `schemeDerivedCategory X` unfolds to
   `DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))`, exactly the
   `def-pc-derived-category` declaration, not D_QCoh or the distinct category instance
   on `X.Modules`. The explicit `HasDerivedCategory.{w}` binder chooses the localization
   required by that declaration. Mathlib `HasDerivedCategory.standard` supplies the
   usual size choice; this is not a geometric restriction on X. PASS.
3. Arbitrary K, L, M: `∀ K L M : schemeDerivedCategory X` within the witness families.
   The witnesses are simultaneous families for all objects, so their following
   naturality equations express the node's functoriality. No boundedness, perfectness,
   flatness or injectivity is imposed on the derived objects. PASS.
4. Derived tensor K tensor^L L: `K ⊗ L` uses the global
   `schemeDerivedTensorMonoidal` from `DerivedTensorStructure`. Opened that definition:
   it specializes the upstream K-flat localization construction to the shared sheaf
   tensor, rather than choosing an arbitrary monoidal structure. Opened
   `CochainComplex.mapBifunctor`, `CochainComplex.IsKFlat`, and
   `CochainComplex.exists_isKFlatResolution` from the dependency records. They give
   total tensor with the stated signs, the acyclic-tensor K-flat predicate, and
   degreewise epimorphic K-flat resolutions with flat terms. These are representative
   conventions, not additional hypotheses on K or L. PASS.
5. Derived internal Hom: `(derivedInternalHom
   (Opens.grothendieckTopology X.toRingedSpace) X.toRingedSpace.sheaf).obj (op L, M)`.
   Opened the recorded definition and its comparison statements: localization of the
   Hom-complex functor after functorial K-injective replacement in the second variable.
   The site is the small category of opens of the underlying space, with the structure
   sheaf as commutative ring sheaf. This is the node's RHom, including its contravariant
   first argument; no private copy is used. PASS.
6. First canonical functorial bijection: witness
   `e : ∀ K L M, (K ⟶ RHom(L,M)) ≃ (K ⊗ L ⟶ M)`.
   `Equiv` expresses a bijection of the precise Hom sets. The first conjunct says
   `e K' L' M' (a ≫ f ≫ RHom.map (b.op,c)) = (a ⊗ₘ b) ≫ e K L M f ≫ c`
   for `a : K' ⟶ K`, `b : L' ⟶ L`, `c : M ⟶ M'`. All compositions and
   variances agree with source and target; setting two maps to identities recovers
   naturality in each individual variable. PASS.
7. Canonical tensor symmetry, functorial in K and L: witness
   `s : ∀ K L, K ⊗ L ≅ L ⊗ K`; second conjunct
   `(a ⊗ₘ b) ≫ (s K' L').hom = (s K L).hom ≫ (b ⊗ₘ a)`.
   The two sides run from K tensor L to L' tensor K'. The docstring specifies the
   Koszul-sign symmetry of representatives and its descent. No extra hexagon or
   involutivity assertion, which the item does not request, is added. PASS.
8. Final functorial bijection: witness
   `e' : ∀ K L M, (K ⟶ RHom(L,M)) ≃ (L ⊗ K ⟶ M)`.
   Third conjunct `e' K L M f = (s K L).inv ≫ e K L M f` has the correct
   symmetry direction, from L tensor K to K tensor L. Final conjunct has tensor map
   `b ⊗ₘ a`, exactly naturality after swapping the tensor factors. PASS.

Edge cases: all three objects may be zero; all quantified maps may be zero or identities.
The empty scheme is admitted. There is no index-set or degree/n binder in this theorem;
its shared unbounded complex constructions include degree zero and all integer degrees.
No characteristic is fixed or excluded. `universe u w` and the explicit localization
binder match the dependency API without forcing the Hom universe to equal the scheme
universe. The opens site fits `SmallCategory`, including for the empty scheme. No
finite-rank or bounded representative assumption appears.

Independent searches used different terms from the first reading:

- LeanFinder, `closed monoidal derived sheaf category Hom equivalence`: eight generic
  sheaf/closed-category hits, none the derived tensor/internal-Hom bijection here.
- Loogle, `CategoryTheory.Adjunction.homEquiv`: the generic adjunction API, no adjunction
  identifying this concrete K-injective `derivedInternalHom`.
- LeanSearch, `Hom into derived sheaf Hom equals Hom from derived tensor product`:
  unavailable (Internal Server Error), recorded by the search script; no absence
  verdict inferred from this unavailable service.
- Mathlib grep, `tensor.*[Hh]om.*[Ee]quiv|derived.*[Aa]djunction` in `Algebra/Homology`:
  no hits. Additional direct rg over Mathlib's monoidal and homology modules, project
  `lean/Sheaf`, and upstream `WeilConjectures` found the ordinary closed-category API,
  existing RHom definition/comparison modules, and upstream
  `DerivedCategory.tensorHomAdjunctionQhObj`.
- Opened upstream `CategoryTheory/DerivedCategory/Monoidal/Closed.lean`, in particular
  `tensorHomAdjunctionQhObj`, its hypotheses, and `monoidalClosed`. It gives an adjunction
  to `internalHomQhObj P` for a homotopy-category representative, not the recorded
  sheaf Hom-complex/K-injective bifunctor. Its own documentation identifies comparison
  to the concrete K-injective model as further work. It therefore cannot serve as an
  existing declaration for this item. The upstream name index and overlaps record
  contain no existing declaration of this item's theorem.

No mathematical mismatch found; no Lean or node statement change was necessary.
No new nodes or dependency modules are in this delivery, and no statement correction
or disputed flag needs a citer review. Left `## Worker report` intact and added this
independent review only. The module has a single named theorem with proof `sorry`,
no definition or hidden data hole, no file-local notation or instance, both imports
are used, and both docstrings cite the source and blueprint. The theorem docstring
tracks all four node proof steps including representative independence and the cone
argument for tensor invariance. All universes and variables are explicitly bound.
The node's `lean.statement` was checked verbatim after whitespace normalization
against the file signature, and every Lean line has at most 100 characters.
Local `lcompile.py` compiled this module successfully (exit 0, no warnings).
