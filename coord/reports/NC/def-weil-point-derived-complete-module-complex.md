## Worker report

The module `Sheaf.RingTheory.DerivedCompleteModuleComplex` defines
`DerivedCategory.IsDerivedComplete` and its degree-zero specialization
`ModuleCat.IsDerivedComplete`. Both definitions have actual predicate bodies; there are no
proofs, sorries, choices of a derived limit, new nodes, or changed natural-language statements.

Clause-by-clause reading of the node:

- The commutative ring is `{A : Type u} [CommRing A]`; the ideal is `(I : Ideal A)`.
- The ordinary derived category of the abelian category of modules is
  `DerivedCategory (ModuleCat.{v} A)`, with `[HasDerivedCategory.{w} (ModuleCat.{v} A)]`
  specifying its chosen localization and morphism universe. Universes `u`, `v`, `w` are
  explicitly bound and independent, so the ring, modules, and localization are not restricted
  to one fixed size. Mathlib supplies the abelian and linear category structures.
- The object is `(K : DerivedCategory (ModuleCat.{v} A))`.
- For each scalar `f : A`, the inverse system is `K := fun _ : ℕ ↦ K` with transition maps
  `fun _ ↦ f • 𝟙 K`. Scalar multiplication is Mathlib's induced `A`-linear structure on the
  derived category, so these are multiplication by `f`, not multiplication by an integer or
  arbitrary chosen endomorphisms. Indexing at zero is the reindexing of the source's tower
  starting at one; every term and transition remains the same.
- `∀ (f : A), f ∈ I →` gives precisely every scalar belonging to the ideal.
- `∀ [HasProduct (fun _ : ℕ ↦ K)] (T : DerivedCategory (ModuleCat.{v} A)),
  IsDerivedLimit (K := fun _ : ℕ ↦ K) (fun _ ↦ f • 𝟙 K) T → IsZero T`
  expresses that every such derived limit is zero using the dependency's actual Roos-triangle
  predicate. The product instance is universally bound inside the predicate, rather than
  added as a hypothesis on `K`. This checks every product presentation without making a
  choice. Countable products exist in `D(A)`; the node does not ask to assert that existence
  or choose a product or derived limit, and neither does this definition. The universal
  product quantification is thus not a vacuous substitute for the intended predicate.
  `IsZero` is categorical vanishing, independent of a chosen zero object.
- For an arbitrary bundled module `(M : ModuleCat.{v} A)`,
  `((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)` is exactly `M[0]`.
  `ModuleCat.IsDerivedComplete I M` applies the preceding predicate to this object.
- This is an ordinary module-derived-category definition. It uses no pro-etale site, sheaf
  category, reduction tower, or coefficient-sheaf completeness predicate.

Dependency declarations read and used:

- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`,
  and `DerivedCategory.singleFunctor`, from `def-weil-abstract-derived-category`.
  The linear extension module publicly imports Basic and equips its localization with
  scalar multiplication. Its declarations and instance signatures were read in full.
- `Sheaf.CategoryTheory.Triangulated.DerivedLimit`: `CategoryTheory.IsDerivedLimit`, from
  `def-weil-derived-limit`. Its body existentially quantifies the two remaining Roos-triangle
  maps and invokes `IsDerivedLimitTriangle`; both definitions and docstrings were read.
  Its imported `towerTransitionEndomorphism` is `1 - towerProductShift`, with the latter's
  nth projection the next projection followed by the transition, giving the required sign.
- Supporting Mathlib imports give `Ideal`, `ModuleCat`'s abelian structure, and the canonical
  derived linear structure. No private copies or file-local instances are introduced.

Source checked directly: `literature/stacks-project/more-algebra.tex`, opening of
`section-derived-completion` (Tag 091N), and `definition-derived-complete` (Tag 091S).
The former introduces `T(K,f)` as the derived limit of the multiplication tower; the latter
requires its vanishing for every `f ∈ I` and defines module completeness via `M[0]`.

Edge cases checked mathematically before writing:

- `f = 0`: the transition endomorphism of the product is the identity, so its derived-limit
  object is zero. Consequently `I = ⊥` imposes no unintended extra restriction.
- A unit in `I`, in particular `I = ⊤`: the multiplication tower has invertible transitions
  and its homotopy limit is isomorphic to `K`; completeness forces `K` to be zero, as intended.
- The zero object and zero module satisfy the intended predicate for every ideal; the zero
  ring is permitted, and all its modules are zero. There is no nontriviality hypothesis.
- Infinitely generated ideals and unbounded complexes are included: no finite-generation,
  Noetherian, boundedness, torsion, or adic-completeness assumption appears.
- The degree-zero module clause introduces no boundedness constraint on the first predicate.

Searches for an existing notion (all on 2026-10-15):

- `msearch.py`, LeanFinder: "Derived completeness of complexes of modules over a commutative
  ring with respect to an ideal by vanishing of multiplication tower homotopy limits".
  Eight hits: `IsAdicComplete`, `IsAdicComplete.toIsPrecomplete`, `AdicCompletion.map_exact`,
  `isAdicComplete_iff`, `Hausdorffification`, `AdicCompletion.module`, `IsPrecomplete`,
  `AdicCompletion`. These concern ordinary module completion, not the node's predicate.
- `msearch.py`, Loogle: `"DerivedComplete"`; zero hits.
- `msearch.py`, Mathlib grep: `derived.?complete|DerivedComplete|derivedComplete`; zero hits.
- `msearch.py`, LeanSearch: "Derived complete complexes of modules with respect to an ideal";
  unavailable, Internal Server Error; no mathematical verdict inferred from that failure.
- `rg` over the project's `lean/Sheaf` and upstream `WeilConjectures` for
  `derived.complete|DerivedComplete|derivedComplete|IsDerivedLimit`: upstream has sheaf
  completeness and related coefficient transport, not this module-category predicate.
  In particular the full docstring and body of
  `CategoryTheory/DerivedCategory/Complete/Defs.lean`'s
  `DerivedCategory.derivedComplete` were inspected: it is an object property on a category
  of sheaves, defined using the reduction tower `K ⊗ᴸ R/Iⁿ`. It is not the present statement.
- `grep -rn def-weil-point-derived-complete-module-complex` over upstream `WeilConjectures`:
  no hits.
- `rg IsDerivedComplete|isDerivedComplete` over Mathlib, upstream `WeilConjectures`, and
  `lean/Sheaf`, and `rg IsDerivedComplete dag/lean_names_upstream.json`: no name collision.

No statement dispute, unusable dependency, or correction was found. Compilation and the
required delivery dry run are performed with the authorized server-only tools; no local
Lean compiler or library build is used. The second reading is reserved for the next worker.

## Second reading by NC

I independently read the repository node, its sandbox copy, the delivered Lean file,
Stacks more-algebra.tex at section-derived-completion and definition-derived-complete
(Tags 091N and 091S), both statement-dependency nodes and their recorded declarations.
The source introduces no Noetherian, finite-generation, boundedness, or nontriviality
hypothesis here. The commutative-ring convention agrees with the node.

The objects, hypotheses and defining clauses, in order, are:

1. A commutative ring A: `{A : Type u} [CommRing A]`. Exact; no field or characteristic
   restriction.
2. The ordinary derived category of A-modules: `DerivedCategory (ModuleCat.{v} A)` under
   `[HasDerivedCategory.{w} (ModuleCat.{v} A)]`. Exact. I opened Basic.lean: the dependency
   is localization of integer cochain complexes at quasi-isomorphisms, with the chosen
   morphism universe. Its standard localization is available at a sufficiently large
   universe. The independent module universe does not exclude large modules.
3. K in that category: `(K : DerivedCategory (ModuleCat.{v} A))`. Exact; unbounded.
4. A scalar f and its constant multiplication tower: `fun _ : ℕ ↦ K` and
   `fun _ ↦ f • 𝟙 K`. Exact. Linear.lean induces A-linearity from ModuleCat through
   localization and makes Q linear, so this is the required scalar multiplication.
   Reindexing the source's positive integers by natural numbers changes no term or map.
5. An ideal and every scalar in it: `(I : Ideal A)` and `∀ (f : A), f ∈ I →`.
   Exact, including arbitrary infinitely generated ideals.
6. Every derived limit is zero: the universally bound product witness and object T,
   followed by `IsDerivedLimit ... T → IsZero T`. Exact. I opened DerivedLimit.lean:
   IsDerivedLimit existentially quantifies p and delta and asserts the distinguished
   Roos triangle. I also opened TowerTransitionEndomorphism.lean: its middle arrow is
   identity minus the shift with nth projection `pr (n+1)` followed by f. Thus this is
   the dependency's actual notion, with the right sign. Quantifying over HasProduct
   does not assume an extra property of K: countable products exist in D(A), and
   product witnesses are propositions. The node explicitly asks for every such limit,
   not for a chosen object or a separate existence assertion.
7. An A-module M and its degree-zero specialization: `(M : ModuleCat.{v} A)` and
   `DerivedCategory.IsDerivedComplete I ((DerivedCategory.singleFunctor ... 0).obj M)`.
   Exact. I opened the singleFunctor declaration and its Q_obj_single_obj description:
   it places M in degree zero and then localizes. No sheaf category is substituted.

Edge cases: I = bottom and f = 0 give the identity middle map and hence zero limit;
a unit f gives the constant tower up to isomorphism and forces K to vanish. The zero
object/module is permitted for every ideal; the zero ring is permitted. No boundedness,
finiteness, characteristic or nonzero condition is present. There is no variable index
set or scheme, so empty index sets and empty schemes are not extra cases of this node.
The fixed tower is countable; its product fits the module universe. All three universes
and every variable are explicitly bound. No additional size restriction is imposed.

Independent duplicate searches on 2026-10-15:

- LeanFinder via msearch.py: "Complex K is complete for ideal I if Hom and Ext from A
  localized at every element of I vanish". Eight results: injective dimension, Ext,
  localCohomology.diagram, IsPrecomplete and IsAdicComplete; none is this predicate.
- Loogle via msearch.py: `"IsDerivedComplete"`; zero hits.
- Direct rg in Mathlib/RingTheory and project lean/Sheaf/RingTheory with
  `derived.?complete|complete.*complex|multiplication.*tower`, and broader searches in
  project lean/Sheaf and upstream WeilConjectures for derived completeness: no existing
  multiplication-tower completeness predicate. Name searches in those trees and
  dag/lean_names_upstream.json found no IsDerivedComplete collision.
- I opened the upstream Complete/Defs.lean declaration `DerivedCategory.derivedComplete`
  and its context: its argument is a derived sheaf object and it asserts that the
  reduction cone to K tensor R/I^n is a homotopy limit. It does not state this node's
  ordinary-module multiplication-tower predicate. Ordinary IsAdicComplete likewise
  does not replace this predicate. The worker's LeanSearch service failure remains
  recorded above; no mathematical conclusion rests on it.

No mismatch found; no Lean or node changes required. There are no new nodes or dependency
modules, no corrected statement, no theorem proofs, no hollow data, and no sorries.
Both declaration docstrings and the module docstring identify their source and blueprint;
the node has no proof steps to transcribe. The recorded lean.statement agrees verbatim
with the main declaration signature under the project's signature-reader convention.
Server-only scompile.py and deliver2.py checks are run for this delivery.
