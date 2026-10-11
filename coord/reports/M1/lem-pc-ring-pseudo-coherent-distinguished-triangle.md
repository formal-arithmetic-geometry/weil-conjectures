## Worker report

The module `Sheaf.RingTheory.PseudoCoherentDistinguishedTriangle` defines
`CategoryTheory.IsMPseudoCoherent` for an object of the derived category of
`R`-modules.  A witness is a cochain complex `E`, integers `a,b`, and a map
`Q.obj E ⟶ C`; the complex is zero outside `[a,b]`, every term is finite free,
the induced homology map is an isomorphism in degrees `i > m`, and the degree
`m` homology map is epi.  The theorem
`CategoryTheory.isMPseudoCoherent_of_distinguished_triangle` states all three
clauses of the node for a distinguished `Triangle` in `DerivedCategory`:

* the first implication renders `(m+1)`-pseudo-coherent `T.obj₁` and
  `m`-pseudo-coherent `T.obj₂` implying `m`-pseudo-coherent `T.obj₃`;
* the second renders `m`-pseudo-coherent `T.obj₁` and `T.obj₃` implying the
  same property for `T.obj₂`;
* the third renders `(m+1)`-pseudo-coherent `T.obj₂` and `m`-pseudo-coherent
  `T.obj₃` implying `(m+1)`-pseudo-coherent `T.obj₁`.

The ring hypothesis is `(R : Type u) [Ring R]`; the integer index is
`(m : ℤ)`.  `hT : T ∈ distTriang (DerivedCategory (ModuleCat R))` renders
the distinguished-triangle hypothesis.  The proof is `sorry` as required;
its docstring records the mapping-cone, long-exact-sequence, five-lemma,
four-lemma, and rotation argument from Tag 064R.

Dependency used: `def-weil-abstract-derived-category` is the Mathlib
declaration `DerivedCategory` from
`Mathlib.Algebra.Homology.DerivedCategory.Basic`; the module uses its `Q`,
`homologyFunctor`, and distinguished-triangle infrastructure.

Edge cases checked: arbitrary integer `m` (including `m = 0` and negative
indices), empty or zero complexes (covered by the explicit finite support and
`IsZero` conditions), and arbitrary rings including the zero ring.  No index
set or characteristic restriction is introduced.

Searches: `msearch.py leanfinder` for “distinguished triangle ...
m-pseudo-coherence” found only generic derived-category declarations;
`msearch.py loogle` for `DerivedCategory.mem_distTriang_iff` found no
pseudo-coherence theorem; grep of Mathlib for `pseudo.?coherent|mapping.?cone`
found cone infrastructure but no pseudo-coherence declaration; `rg` over
`WeilConjectures` and project `lean/Sheaf` found no existing declaration.
Therefore a new module was required.

## Earlier second reading (a previous round; superseded)

The module and node were reread independently.  The ring, integer, triangle,
and distinguished hypotheses match the node, and the three implications occur
in the same order with the same shifted indices.  The witness definition
spells out bounded finite-free complexes and the required isomorphism and
epimorphism conditions.  No mismatch was found.


## Second reading by M1

Independent reading of the node JSON, the delivered Lean, the sole statement
 dependency node `def-weil-abstract-derived-category`, its Mathlib declarations,
and Stacks `more-algebra.tex` lines 15854–15978 (read from the server).
Definition 064Q(1) and Lemma 064R give exactly the inline definition and all
three assertions. The section introduces a ring, with no Noetherian,
characteristic, boundedness-of-the-target, or finite-generation hypothesis.
The node has no statement correction. No new nodes or dependency modules
were supplied or needed: the notion of m-pseudo-coherence is already explicitly
defined by this item's own statement, and its derived-category dependency is
usable as recorded.

Object, hypothesis, and conclusion checklist (all verdicts: match):

1. Ring R: `(R : Type u) [Ring R]`. No field or finiteness assumption.
2. Integer m: `(m : ℤ)`, including negative integers.
3. The abelian category of R-modules and its derived category:
   `ModuleCat.{v} R`, `DerivedCategory (ModuleCat.{v} R)`, with
   `[HasDerivedCategory.{w} (ModuleCat.{v} R)]`. Read
   `DerivedCategory/Basic.lean`: `HasDerivedCategory` chooses a localization,
   `DerivedCategory` is the localization, and `Q` is its functor. The choice
   is size infrastructure, always available via `HasDerivedCategory.standard`,
   not a new mathematical hypothesis. All u, v, w are declared explicitly.
4. Witness E: `∃ (E : CochainComplex (ModuleCat.{v} R) ℤ) (a b : ℤ)`.
   Boundedness is `∀ i, i < a ∨ b < i → IsZero (E.X i)`; vanishing means the
   zero module up to unique isomorphism, as for complexes of abstract modules.
5. Finite free in every degree: `∀ i, Module.Free R (E.X i) ∧
   Module.Finite R (E.X i)`. Finite generation together with freeness is
   precisely finite freeness; it does not require a chosen basis.
6. A derived morphism from E to the object: `(f : DerivedCategory.Q.obj E ⟶ C)`.
   It is not an unnecessarily specified chain map or a quasi-isomorphism.
7. Cohomology isomorphisms above m: `∀ i, m < i → IsIso
   ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).map f)`.
   Read `DerivedCategory/HomologySequence.lean` lines 34–41: this functor
   factors cochain cohomology through Q. Thus its homological name has the
   cohomological indexing required here.
8. Surjectivity in degree m: `Epi ((DerivedCategory.homologyFunctor
   (ModuleCat.{v} R) m).map f)`. Read `ModuleCat/EpiMono.lean:50`:
   `ModuleCat.epi_iff_surjective` identifies this with actual surjectivity.
9. Triangle A → B → C → A[1]: `(T : Triangle (DerivedCategory
   (ModuleCat.{v} R)))`, with A, B, C exactly `T.obj₁`, `T.obj₂`, `T.obj₃`.
   Distinguished: `(hT : T ∈ distTriang (DerivedCategory (ModuleCat.{v} R)))`.
   The dependency's triangulated instances and `mem_distTriang_iff` supply
   precisely the standard cone-derived notion, not an arbitrary triangle class.
10. First conclusion: `IsMPseudoCoherent R (m + 1) T.obj₁ →
    IsMPseudoCoherent R m T.obj₂ → IsMPseudoCoherent R m T.obj₃`.
11. Second conclusion: `IsMPseudoCoherent R m T.obj₁ →
    IsMPseudoCoherent R m T.obj₃ → IsMPseudoCoherent R m T.obj₂`.
12. Third conclusion: `IsMPseudoCoherent R (m + 1) T.obj₂ →
    IsMPseudoCoherent R m T.obj₃ → IsMPseudoCoherent R (m + 1) T.obj₁`.
    The three implications are conjoined under the same universally bound
    ring, integer, and distinguished triangle, in the node's order.

Edge cases: zero complexes and zero objects are allowed (`IsZero`, zero-rank
free modules); a witness may have empty support, and no condition a ≤ b is
needed to express it. Every integer, including 0 and negative integers, is
covered. The zero ring and every characteristic are allowed. There is no
index family or scheme, so empty index sets and empty schemes introduce no
extra case here. Module carriers and localized hom universes are independent
parameters v and w, rather than fixed to the ring's universe.

Independent searches: `msearch.py leanfinder` query “bounded finite free
approximation cohomology surjective pseudo coherent triangle” returned only
fraction/factorization infrastructure, no matching notion or theorem.
`msearch.py leansearch` query “pseudo coherent complex of modules” returned
Internal Server Error (recorded unavailable, not a negative search verdict).
`msearch.py grep` query `pseudo.?coher|IsMPseudo|finite.?free.*approx` returned
no Mathlib hits. Direct `rg` for `IsMPseudoCoherent`, `PseudoCoherent`, and
`pseudo_coherent` over Mathlib, WeilConjectures and project lean/Sheaf found
no existing declaration. A broader pseudo-coherence grep in WeilConjectures
found only an informal direct-image comment. DAG definition searches found
`def-pur-pseudo-coherent-complex`, which concerns sheaves on schemes and full
pseudo-coherence, not m-pseudo-coherence of ring complexes; it is not a usable
replacement. `dag/lean_names_upstream.json` has no name collision.

Mismatches repaired: removed the undocumented global `derivedModuleCat`
instance which hardwired the standard localization and inferred module size.
Both declarations now use explicit `ModuleCat.{v} R` and chosen localization
`HasDerivedCategory.{w}`. This retains exactly the dependency's chosen-universe
convention without restricting the theorem to one model of D(R). Added the
required source/blueprint declaration docstring to `IsMPseudoCoherent`.
Expanded the theorem docstring to carry both node proof steps: truncation,
map lift, cone/TR3, cohomology ladder, five-lemma and epi four-lemma, then the
two precise rotations and shifted indices. Added the conventional copyright
header and removed redundant imports. Kept the witness and the three clauses
unchanged. Updated `lean.statement` verbatim to the new theorem signature.
No data is sorry; the only theorem has proof `by sorry`, as stage 2 requires.
Remote single-file compilation passed cleanly (1.4 s); all lines are at most
100 characters and every variable and universe is explicitly bound.

## Reviewer fix (R-pdt0910)

The delivery carried a private copy `CategoryTheory.IsMPseudoCoherent` of the notion
landed meanwhile as `DerivedCategory.IsMPseudoCoherent` (def-pc-ring-m-pseudo-coherent,
module `Sheaf.RingTheory.MPseudoCoherent`, on the base). The copy is dropped; the theorem
now imports and uses the landed definition (same witness: bounded finite-free complex,
isomorphisms above m, epi at m), and `[Ring R]` became `[CommRing R]` as that definition
requires (Stacks rings are commutative). Clauses, indices and universes unchanged.
