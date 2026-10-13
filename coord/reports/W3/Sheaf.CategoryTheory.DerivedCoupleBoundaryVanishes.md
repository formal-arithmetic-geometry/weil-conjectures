## What changed

Proved `CategoryTheory.BigradedExactCouple.derived_couple_boundary_vanishes`
in `Sheaf.CategoryTheory.DerivedCoupleBoundaryVanishes`, with its signature and
existing docstring unchanged. Added the proof-only import
`Sheaf.CategoryTheory.DerivedCoupleMapConstruction`. Apply its proved
`CategoryTheory.derivedCoupleBackward_exists` to the original couple, precompose
its descent equation by the kernel inclusion of the image epimorphism, and
cancel the equality transport. Updated the item's DAG proof and proof dependencies
accordingly. No definitions, public imports, or other modules changed.

The LeanFinder search for kernel/image boundary vanishing returned generic short-complex
image-to-kernel lemmas, not an exact-couple theorem. Loogle found `kernel.condition`.
Local searches of Sheaf, WeilConjectures and Mathlib found the already proved backward-map
construction. The import-direction check permits this import. The module compiled cleanly
with lcompile.py. The proof works for all integer indices, including negative ones, and
all natural types, including zero; it uses no nonzero-object assumptions.

## Proved and sorry left

Closed one hole:
`CategoryTheory.BigradedExactCouple.derived_couple_boundary_vanishes`
(node `lem-sp-derived-couple-boundary-vanishes`). No sorries remain in the item.
No holes added or split off; this is a proof from an already proved construction.

## No longer needed

The planned dependency `lem-sp-derived-couple-exact`, module
`Sheaf.CategoryTheory.DerivedCoupleExact`, is not needed for this proof.
It was not imported in the original item, so there is no import line to remove.
The sole existing public import `Sheaf.CategoryTheory.ExactCouple` remains needed
for the statement. No claim is made that DerivedCoupleExact is globally unreachable.
No other planned dependencies are pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof dependency on `lem-sp-derived-couple-exact` was circular:
`Sheaf.CategoryTheory.DerivedCoupleExact` imports this item and uses its theorem.
The construction of the backward map supplies an independent and already proved route.

`lem-sp-derived-map-construction` is used as a generic tool: its raw-family descent
equation specializes exactly to the couple's alpha, f, g and dInto. Its node is
filed under another chapter/unit, but this reuse does not replace any proper-base-change
unit statement or step. The maintainer may record this accepted tool use; this delivery
does not edit tool_uses. No new nodes or change records are necessary.

## Second reading by W3

1. **Visible declarations unchanged: PASS.** Read the complete delivered module and
   compared it with the repository using `diff -u`; also compared the theorem signature
   byte for byte. The universes, category and abelian instances, natural type `s`, couple
   `X`, integer quantifiers, and all three morphisms in the conclusion are unchanged.
   There is one added plain import and one replaced proof. No definition or public
   import changed; there are no other delivered modules or change records.
2. **Proof and axioms: PASS.** Independently compiled the module with `lcompile.py`
   (1.3 seconds, no errors or warnings). Compiled a scratch copy with `#print axioms`
   for `CategoryTheory.BigradedExactCouple.derived_couple_boundary_vanishes` and
   `CategoryTheory.derivedCoupleBackward_exists`: both list exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered module has
   no `sorry`, axiom declaration, unsafe/opaque declaration, or implementation override.
   Read the backward-map construction: its image descent is proved by the cokernel
   universal property of an exact short complex. The existential map is eliminated
   within a proposition here; no data definition or arbitrary witness is introduced.
3. **Split statements: PASS, none.** No new statement, node, or hole is added.
   Checked the existing descent theorem's hypotheses individually: `dInto_comp_d`
   supplies `hβ`, `f_g_zero` supplies `hg`, `exact_alpha` supplies `ha`, and unfolding
   `dInto` and `d` supplies the incoming-differential formula by reflexivity. Thus this
   is an application of a proved construction, not a renamed unproved item. The proof
   covers `s = 0`, negative integer indices, and zero objects: all reindexings are
   unrestricted integer identities and no nonzero or positivity hypothesis is used.
4. **Shortest route, imports and pruning: PASS.** Read Stacks Tags
   [011R](https://stacks.math.columbia.edu/tag/011R) and
   [0AMJ](https://stacks.math.columbia.edu/tag/0AMJ), especially the latter's footnote:
   exactness identifies the kernel of alpha with the image of f, and g carries that
   indeterminacy into the incoming differential, killed by the cycle quotient.
   The local literature files are absent, so the official pages were read instead.
   The existing backward-map theorem already performs that calculation, and the
   remaining proof is just kernel.condition followed by mono cancellation of eqToHom.
   Independent `rg` searches in Sheaf, WeilConjectures, the upstream checkout, and
   Mathlib found no shorter applicable exact-couple result. The second-reader msearch
   grep query `kernel.*factorThruImage|boundary.*vanish|desc_image` found the generic
   kernelFactorThruImage isomorphism and image universal properties, which still
   require the boundary calculation. A Loogle query was rejected by its parser and
   is not evidence of absence. Both imports are needed: ExactCouple supplies the
   public signature, and DerivedCoupleMapConstruction supplies the proof theorem
   (the dependency of ExactCouple is a private import). The only old proof dependency,
   lem-sp-derived-couple-exact, is listed under No longer needed; its module imports
   and applies this item, so using it would be circular. Read the proper-base-change
   unit's statement, steps and `realized` record: this item is below those realizations,
   and none is bypassed or edited. The cross-unit construction is only a generic tool.
5. **DAG agreement: PASS.** Compared both node JSON files: only `proof`, `proof_deps`,
   and `proof_origin` differ. The first step names the existing node that records
   derivedCoupleBackward_exists and describes precisely its instantiated descent
   equation. The second step's kernel.condition and cancellation are elementary.
   Their cited-node union is exactly `proof_deps`; the Lean record still contains
   the verbatim unchanged signature. No new-node obligations arise.

Second reading changed only this report by adding the independent checks above.
The proof, imports, and node records required no repair. One original hole closed,
zero holes added, zero split off; the planned derived-couple-exact dependency is pruned.
