## Worker report

The item module `Sheaf.AlgebraicGeometry.AffineSupportIteratedCones` states
`AlgebraicGeometry.Scheme.affine_support_iterated_cones`. Its only theorem proof is `sorry`.
The delivery also supplies one fully written definition node for derived function multiplication
and a dependency module extending the perfect-complex interface to localized open sites.
There are no proofs or hollow definitions in these two modules.

Hypothesis and clause correspondence:

- An affine scheme X = Spec(A): `(X : Scheme.{u}) [IsAffine X]`. We use its canonical
  presentation `X.isoSpec : X ≅ Spec Γ(X, ⊤)`, so `A` is the canonical coordinate ring
  `Γ(X, ⊤)`. This covers every affine scheme and every ring; replacing a specified affine
  presentation by the canonical one transports generators by the canonical ring isomorphism.
- The finite list g_1,...,g_s: `(s : ℕ) (g : Fin s → Γ(X, ⊤))`.
  There is no nonemptiness hypothesis on the generator list.
- The derived category of ALL module sheaves is `schemeDerivedCategory X`, with the shared
  `HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))` binder.
  The corresponding binders for all opens provide the same localization used by `IsPerfect`.
- E and C_0=E are expressed by `C : Fin (s + 1) → schemeDerivedCategory X`, with E identified
  directly with `C 0`; `hE : IsPerfect X (C 0)` expresses its perfection. This substitution
  removes only a redundant equality binder, not an object or a mathematical hypothesis.
- A cone C_i of multiplication by g_i on C_{i-1}: for `i : Fin s`, `i.castSucc` is the
  preceding stage and `i.succ` is the next stage. `m i`, `b i`, `d i` are the triangle maps;
  `hcone` says their triangle belongs to `distTriang (schemeDerivedCategory X)`.
  `hm` says `m i` is derived multiplication by the sectionwise restrictions of `g i`.
  These maps range over arbitrary distinguished triangles, so arbitrary cone choices are covered.
- C_s is perfect: `IsPerfect X (C (Fin.last s))`, the first conjunct.
- T=V(g_1,...,g_s) and cohomology vanishes outside T: the second conjunct quantifies over every
  `n : ℤ` and every point `x : X` in some `X.basicOpen (g i)`. The union of those principal
  opens is exactly X minus the common zero set T. `Subsingleton` of the underlying abelian
  stalk of the `DerivedCategory.homologyFunctor` object means its stalk is zero. Vanishing of
  these stalks is precisely vanishing of the cohomology sheaf on that open. No particular
  scheme structure on T enters the statement, and no extra support predicate is introduced.
- The optional quasi-compact open U: `∀ (U : X.Opens) (_hU : IsCompact (U : Set X)), ...`.
  Compactness of the underlying subset is the topological quasi-compactness of the open subscheme.
- The perfect object F of D(O_U): `F` belongs to the derived category on `moduleRings.over U`;
  `IsPerfectOnOpen X U F` expresses exactly local strictly perfect representability on U.
  This is the same open-site carrier as the recorded `IsPerfect` definition uses for restriction.
- E|U ≅ F ⊕ F[1]: the first `Nonempty` premise uses the shared
  `SheafOfModules.overFunctor ... U |>.mapDerivedCategory` object and `F ⊞ F⟦(1 : ℤ)⟧`.
- Each g_i acts by zero on F: the final premise is
  `∀ i : Fin s, IsDerivedFunctionMultiplication ((moduleRings X.toRingedSpace).over U)
  (fun V ↦ restriction of g i to V.unop.left) F 0`.
  The derived multiplication predicate specifies sectionwise multiplication on every representing
  complex and conjugation through its representative isomorphism. It is not an unconstrained map.
- The restriction of C_s is the stated binomial sum: the concluding `Nonempty` is an isomorphism
  to `biproduct (fun p : (j : Fin (s + 2)) × Fin (Nat.choose (s + 1) j.val) ↦ F⟦(p.1.val : ℤ)⟧)`.
  Its finite dependent index has j=0,...,s+1 with precisely choose(s+1,j) copies of F[j].

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms, and opens;
  `Mathlib.AlgebraicGeometry.AffineScheme`: `IsAffine` and the documented canonical affine
  presentation `Scheme.isoSpec`. The definition and docstrings were read in the pinned source.
- `Sheaf.AlgebraicGeometry.DerivedCategory`: `AlgebraicGeometry.schemeDerivedCategory`.
- `Sheaf.AlgebraicGeometry.PerfectComplex`: `Scheme.IsPerfect`, `Scheme.IsStrictlyPerfect`;
  the new dependency module imports them and defines only `Scheme.IsPerfectOnOpen`.
- `Sheaf.Paper.DerivedHomMayerVietoris`, imported transitively by these modules: `moduleRings`
  and the shared exact restriction instances for `SheafOfModules.overFunctor` and `overMap`.
- The new node's dependencies are `SheafOfModules` from
  `Mathlib.Algebra.Category.ModuleCat.Sheaf` and `DerivedCategory`, `Q` from
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`. Full signatures and docstrings were read;
  `SheafOfModules.instAbelian` is inferred from the canonical Mathlib instance, never chosen.

Edge cases checked before finalizing: s=0 has just C_0, the complement of V(empty)=X is empty,
and the sum is F⊕F[1]. Zero generators give empty principal opens and impose no support vanishing.
A unit generator forces global zero cohomology and the optional annihilation premise forces F=0.
The zero ring/empty affine scheme, the zero object, the empty open U, and zero multiplicities in
finite sums are all allowed by the types. There is no restriction on characteristic or degree,
and the derived hom universe w is arbitrary. A derived object always has a complex representative
(the localization functor Q is essentially surjective), so the multiplication predicate cannot
hold merely through an absence of representatives. For compatible central functions the degreewise
multiplication chain map is unique and natural in chain maps, hence it descends through Q; its
conjugacy condition holds for all representing isomorphisms.

Searches made (actual outputs are also logged in `searches.jsonl`):

- msearch leanfinder, `iterated cones of multiplication by functions perfect complex support
  binomial shifts`: 8 hits on mapping cones, support bounds and fractions, no item match.
- msearch loogle, `CategoryTheory.Triangle, CategoryTheory.Linear`: 0 hits, unknown identifier
  CategoryTheory.Triangle.
- msearch leansearch, `scalar multiplication natural endomorphism derived category sheaves of
  modules`: service unavailable, Internal Server Error.
- msearch grep, `smul|Linear`, Mathlib Algebra/Category/ModuleCat/Sheaf: 3 change-of-rings hits,
  no derived multiplication definition.
- msearch leansearch, `multiplication by a global section on an object of derived category of
  sheaves of modules`: unavailable, Internal Server Error.
- msearch leanfinder with that same query: 8 hits on scalar compatibility, associated sheaves,
  sheafification and sheaf cohomology, none defining the required derived action.
- msearch grep, `smulHom|FunctionMultiplication|scalar.*derived|derived.*scalar`: 25 unrelated
  Mathlib hits; no required definition. Inspection of the Mathlib center/localization API found
  a generic localization of a category-center element, not the function action on module sheaves.
- rg of WeilConjectures found the existing underived `Scheme.Modules.smulHom` in
  AlgebraicGeometry/Cohomology/Defs.lean; its definition, naturality and docstrings were read.
  It is for the whole scheme module category, not the shared derived/open-site category.
  Other derived-scalar hits were completion lemmas for modules over a fixed ring, not O_X-modules.
- rg of lean/Sheaf found only unrelated base-derived-tensor scalar actions. Searches for the
  item id and the three proposed declaration names in Mathlib, WeilConjectures, lean/Sheaf,
  and dag/lean_names_upstream.json found no collisions or existing item statement.
- DAG rg on the multiplication notion found unrelated boundary-derivation and rank-one
  automorphism statements. `tools/blueprint_refs.py search 'derived multiplication'`: zero nodes.

No statement correction and no STATEMENT-DISPUTED flag are needed. The source Tag 08EK was read
at https://stacks.math.columbia.edu/tag/08EK (the local literature texts are not installed).
Its displayed multiplicities have an indexing typo relative to its starting F⊕F[1]; the node
already uses the correct binomial coefficients choose(s+1,j), as checked directly at s=0 and s=1.
The node's proof steps are retained verbatim and rendered in the theorem docstring.

Validation: all three modules compiled together on the project server with exit code 0,
no errors and no warnings; nothing was compiled locally. All temporary edits and outputs for
this worker were confined to its sandbox. No git commands were run by the worker.

## New nodes

`def-sc-derived-function-multiplication` defines `CategoryTheory.IsDerivedFunctionMultiplication`
on a small ringed site, by the sectionwise action of a chain endomorphism on every complex
representative and its compatibility with the representative isomorphism. It is fully written,
uses existing module-sheaf and derived-category definitions, and has no `sorry`. Source: Tag 08EK,
proof, the endomorphisms g_i. The searches listed above and stored in its mathlib_searches found
no existing node or declaration for this shared derived/open-site action. The generic center
localization does not supply the function action itself. The item cites this new node directly.

## Dependency modules

`def-pc-perfect-complex`: the existing `Scheme.IsPerfect` accepts objects only on the whole
scheme; F here lies on the localized open site. `Sheaf.AlgebraicGeometry.PerfectComplexOnOpen`
imports its existing definitions and adds `Scheme.IsPerfectOnOpen`, using exactly the recorded
strictly perfect complexes and restriction to smaller opens by `overMap`. All existing definitions
remain available from the import, and the dependency node changes only its lean record, with
an explanatory note. The local criterion, the strictly perfect complexes, and the module carrier
are those of the dependency node; no replacement O_X-module or derived category is introduced.

## Second reading by C1

I independently read the base node, all three delivered modules, the dependency records,
`PerfectComplex.lean`, `DerivedCategory.lean`, the restriction definitions in Mathlib,
and the source's `Scheme.Modules.smulHom`. I fetched the Stacks `.tex` sources into this
sandbox because the local literature checkout contains only its index files. In
`perfect.tex`, label `lemma-lift-perfect-complex-plus-shift-support` (08EK), I read the
whole proof and the opening of its section. In `cohomology.tex`, I read
`definition-strictly-perfect` (08C4) and `definition-perfect` (08CM). No section-wide
Noetherian, field, or characteristic assumption applies. The finite generator list
already ensures that the complement of T is quasi-compact; the source's support
hypothesis on F is implied by the explicit annihilation premise. The node extracts the
cone construction, rather than the subsequent lifting of beta and gamma. Its binomial
index s+1 agrees with the explicit first cone in the source, despite the source's later
indexing typo. No statement correction is needed.

My object/hypothesis/conclusion checklist, with each verdict:

1. X = Spec(A), an arbitrary affine scheme: `X : Scheme.{u}` and `[IsAffine X]`.
   `g` takes values in `Γ(X, ⊤)`. Mathlib's `Scheme.isoSpec` identifies this canonical
   coordinate ring with any specified affine presentation. Verdict: the same objects;
   no restriction to a particular ring or affine presentation.
2. A finite list g_1,...,g_s and its common zero set T: `s : ℕ`,
   `g : Fin s → Γ(X, ⊤)`. The support conclusion uses
   `∃ i : Fin s, x ∈ X.basicOpen (g i)`, exactly the complement of T.
   I read `Scheme.basicOpen` and its unit-germ criterion. Verdict: no generator or
   support clause omitted; a separate closed-subscheme structure is unnecessary.
3. E in the derived category of all O_X-modules: `C : Fin (s + 1) →
   schemeDerivedCategory X`, with E identified with `C 0`, and
   `hE : IsPerfect X (C 0)`. The recorded derived-category abbreviation is precisely
   `DerivedCategory (SheafOfModules (moduleRings X.toRingedSpace))`, not its QCoh
   subcategory. Verdict: the same category and perfectness hypothesis.
4. C_0=E and each C_i an arbitrary cone of multiplication by g_i:
   `i.castSucc` and `i.succ` index consecutive objects; `m`, `b`, `d`, and `hcone`
   give the whole distinguished triangle. `hm` fixes the first map by sectionwise
   restrictions of `g i`. Verdict: arbitrary cone choices covered, with no equality
   or additional splitting assumed.
5. C_s perfect: the first conjunct is `IsPerfect X (C (Fin.last s))`.
   Verdict: exact conclusion.
6. All cohomology sheaves of C_s vanish outside T: the second conjunct quantifies
   over `n : ℤ` and `x : X`, and requires `Subsingleton` of the underlying additive
   stalk of the homology sheaf on the union of the principal opens. An additive
   group is zero exactly when its carrier is subsingleton, and stalkwise vanishing
   detects sheaf vanishing. Verdict: exact conclusion, including negative degrees.
7. Optional quasi-compact open U: `∀ U : X.Opens, IsCompact (U : Set X) → ...`
   (the proof is a binder `_hU`). Verdict: the topological quasi-compactness of U,
   without an affine-open or nonempty-open restriction.
8. F perfect in D(O_U): the F binder uses the localized module-ring sheaf,
   and `IsPerfectOnOpen X U F`. Verdict: exact local perfectness notion, as checked
   separately below; no global strictly perfect model imposed.
9. E|U isomorphic to F ⊕ F[1]: the first `Nonempty` premise uses the recorded
   exact `overFunctor.mapDerivedCategory`, `C 0`, and `F ⊞ F⟦(1 : ℤ)⟧`.
   Verdict: exact premise; no selected isomorphism needed.
10. Every g_i acts as zero on F: the final premise applies
    `IsDerivedFunctionMultiplication` on the localized site with endomorphism `0`.
    The scalar family restricts the global section to `V.unop.left`.
    Verdict: zero in D(O_U), rather than zero only on cohomology.
11. C_s|U is the indicated binomial direct sum: the last `Nonempty` conclusion
    has dependent index `(j : Fin (s + 2)) × Fin (Nat.choose (s + 1) j.val)` and
    summand `F⟦(j.val : ℤ)⟧`. Verdict: exactly j=0,...,s+1 and the required
    multiplicities; finite biproducts give the finite direct sum.

The HasDerivedCategory binders share the chosen hom universe w and the canonical
Mathlib Abelian instances. They specify the common localization interface used by
all dependency declarations; they impose no extra geometric hypothesis. All module,
point, function, and complex variables are explicitly bound.

New-node review: `def-sc-derived-function-multiplication` has the required definition
fields, the same chapter/unit, empty proof fields, and is cited by the item. Its
quantifiers over K, e, the chain map, degree, open, and section agree with its Lean
body. For the compatible central families used here, scalar multiplication commutes
with restriction and differential, hence supplies the unique sectionwise chain map.
It descends through localization and commutes with every representative isomorphism.
Q is essentially surjective, so this predicate cannot be vacuously satisfied by
an object without representatives. The arbitrary-family generality of the predicate
adds no premise to the item, where the families are explicitly compatible restrictions.
It contains no postponed data or hidden proof.

Dependency-module review: the original `IsPerfect` takes only an object on X, so it
cannot directly type the F binder on the over-site. `IsPerfectOnOpen` quantifies only
over x in U and neighbourhoods V≤U; its models use the existing `IsStrictlyPerfect`,
with exactly boundedness and direct summands of finite free modules. Mathlib's
`overMap (homOfLE hVU)` restricts from U to V. Thus it specializes the existing
perfect-complex notion to the open-site carrier, while importing all original
definitions. The dependency note explains this interface extension. No second
strictly perfect definition or chosen Abelian instance is introduced.

Edge cases: s=0 leaves C_0 and imposes no support vanishing, since T=X; its direct
sum has two summands F and F[1]. For s=1 the multiplicities are 1,2,1, agreeing
with the explicit first cone in 08EK. Zero generators impose no principal-open
vanishing; a unit generator gives vanishing everywhere and forces F=0 under the
annihilation premise. Zero objects, the zero ring/empty scheme, U=∅, and zero
multiplicities are admitted. There is no nonemptiness, characteristic, degree, or
independent small-index universe restriction. Both u and the localization universe
w remain arbitrary as in the recorded dependency interfaces.

Independent searches (different queries from the first reader):

- msearch leanfinder, `Koszul complex successive mapping cones scalar endomorphism
  binomial decomposition`: eight mapping-cone differential/component lemmas;
  none states this support and binomial theorem.
- msearch loogle, `"smul", "DerivedCategory"`: zero hits.
- msearch leanfinder, `central section acting on localization derived sheaf
  endomorphism`: eight tilde/localization and sheafification hits; no derived
  function multiplication predicate.
- msearch leanfinder, `perfect object locally strictly perfect on open restriction`:
  eight local-to-affine scheme-property lemmas; no open-site perfectness definition.
- rg of Mathlib Homology/AlgebraicGeometry, WeilConjectures, and lean/Sheaf for
  Koszul, scalar/cone combinations, and the three declaration names found no exact
  item or new definition. The existing project Koszul complex is an exterior-power
  complex over a fixed ring; upstream ProjectiveSpace/Koszul is the twisting-sheaf
  short exact sequence. Neither states the item. I also searched the DAG for the
  derived multiplication and open-perfect notions: the existing perfect-complex
  node is the one extended here, and no node supplies the derived function action.
- I opened Mathlib `CatCenter.localization` and its `localization_app` signature:
  it descends an already supplied central natural transformation, without providing
  the function action on module sheaves. Upstream `Scheme.Modules.smulHom` is the
  underived whole-scheme action, not a declaration on the shared derived over-site.
  The added predicate does not duplicate either notion.

Mismatches and changes: none found in the statements, definitions, or node records.
I retained all three Lean modules and their signatures unchanged, and added only
this independent reading to the report. Module/declaration docstrings have the
source and blueprint tags; the theorem docstring covers each of the node's three
proof steps. Only the item's theorem is sorry, and no theorem is proved.

Validation: scompile compiled all three modules together, in dependency order,
on the project server (exit code 0, 5.6 seconds), with no errors or warnings.

## Reviewer fix (R-sic)

The statement was restated on the shared declarations; the two extra modules were left out.

- `IsDerivedFunctionMultiplication` (new node def-sc-derived-function-multiplication) duplicated the landed
  def-sc-derived-global-scalar (`AlgebraicGeometry.schemeDerivedScalar`, J1, used by the 08EJ sibling
  lem-sc-perfect-into-support-on-T). The node was dropped (H12). The cone triangles are now
  `Triangle.mk (schemeDerivedScalar X (g i) (𝟙 (C i.castSucc))) (b i) (d i)`, so the free `m`/`hm` binders are gone.
  The functions `g i` are compatible families (`RingCat.sectionsSubring`), the encoding the 08EJ sibling uses.
- `IsPerfectOnOpen` (dependency module of def-pc-perfect-complex) was a second spelling of perfectness on an open (H4/H13).
  It was reverted and dropped. F is now `schemeDerivedCategory U.toScheme` with `IsPerfect U.toScheme F`. Restriction is
  `overFunctor ⋙ (Modules.overEquiv U).functor` followed by `mapDerivedCategory`, exactly as in the siblings
  lem-sc-affine-perfect-plus-shift and lem-sc-affine-perfect-support-extension.
- "g_i is zero on F" is `schemeDerivedScalar U.toScheme (g' i) (𝟙 F) = 0`. Here `g' i` is the restriction of `g i`
  to U, tied by `(g' i).val (op ⊤) = U.ι.appTop.hom ((g i).val (op ⊤))`; a compatible family is determined by its
  top value.
- U and its HasDerivedCategory infrastructure binders are now top-level. Quasi-compactness of U stays a premise of
  the third clause only.
