## What changed

Proved `CategoryTheory.Sheaf.Torsor.etale_inverse_image_lifting_torsor` with its signature unchanged. Added the proved underlying fibre comparison in `Sheaf.CategoryTheory.Sites.EtaleInverseImageLiftsFibre`, imported privately for the proof. Its private helpers construct the constant-section map and subtype inclusion and prove the equalizer universal property. Set inverse image preserves that equalizer; the underlying abelian comparison and adjunction equations identify its diagram. The main proof transports the given torsor isomorphism and derives equivariance from the inclusion equation and additivity.

## Proved and sorry left

Closed the sole original hole, `CategoryTheory.Sheaf.Torsor.etale_inverse_image_lifting_torsor` (lem-sc-etale-inverse-image-lifting-torsor). The new `CategoryTheory.Sheaf.Torsor.etale_inverse_image_lifts_fibre` (lem-sc-etale-inverse-image-lifts-fibre) is proved. No sorry remains in either delivered module; no holes added. Existing imported theorem holes are not changed.

Edge cases: zero kernel, zero quotient, empty schemes and empty sets of lifts require no nonemptiness assumption in the equalizer proof; the subtype universal property works uniformly. No injectivity of the middle sheaf after pullback is used.

## No longer needed

All three original public imports are retained for the unchanged signature. Removed the private import Sheaf.AlgebraicGeometry.EtaleInverseImageExact and replaced the direct private import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures with the private fibre-helper import; AlgebraicStructures remains imported by that helper. No unit step bypassed. The parent's direct proof-dependency edges to lem-sc-torsor-h1 and lem-weil-pbc-etale-inverse-image-algebraic-structures move to the proved fibre lemma, so their modules remain transitively needed. The standalone prop-weil-pbc-inverse-image-exact / Sheaf.AlgebraicGeometry.EtaleInverseImageExact is not needed for this argument: the original signature already uses the source-library exactness instance through hS.map_of_exact. It was explicitly imported in the repository baseline and is removed in this delivery. The old proof-dependency node prop-weil-pbc-inverse-image-exact is no longer used; its module Sheaf.AlgebraicGeometry.EtaleInverseImageExact is pruned from this argument (other target routes may still import it). The addition-operation comparison clauses are not needed; equivariance is derived from additive unit components and the fibre inclusion equation. No other planned modules are pruned.

## Where the brief, the DAG or earlier work was wrong

The plan was mathematically sound, but its proof dependencies did not directly state the specialized subtype/equalizer comparison. Implemented it as a proved helper module. The separate abelian exactness theorem is redundant given the existing source-library exactness instance. The DAG was updated to match the actual proof.

## New nodes

lem-sc-etale-inverse-image-lifts-fibre: proved underlying fibre comparison, a strict part of the original argument that asserts no action compatibility or transport of arbitrary torsors. Its module is lean/Sheaf/CategoryTheory/Sites/EtaleInverseImageLiftsFibre.lean. No change records are needed; existing signatures and public imports are unchanged.

## Second reading by A3

1. PASS: diffed the existing module against the repository. The theorem signature and
   docstring are byte-for-byte unchanged; the only changes are private proof imports
   and the proof body. No existing definition or target statement changes. The new
   module states only the strictly smaller underlying-fibre comparison.
2. PASS: both modules compile locally through lcompile.py without errors or warnings.
   Neither contains sorry, axiom, unsafe, opaque, implemented_by or extern. Scratch-copy
   #print axioms checks of both public theorems show propext, Classical.choice,
   Quot.sound and inherited sorryAx; no claim of a fully axiom-closed target is made.
   The fibre maps and universal-property lifts are explicitly constructed. The
   existential comparison is eliminated inside a theorem proof, not used to define
   arbitrary data from an unproved existence statement.
3. PASS: no statements with sorry are split off. Read the new fibre theorem and its
   complete docstring argument: the equalizer condition is exactly g(t)=s restricted
   to the object; its universal property supplies the unique subtype lift. Zero
   kernel, zero quotient, empty lift fibres and the empty scheme require no additional
   hypothesis. The helper asserts neither arbitrary-torsor transport nor equivariance,
   which are proved in the original module. Independent leanfinder search for a
   subtype/global-section equalizer comparison and loogle search for Fork/IsLimit,
   plus rg over the library and Mathlib sites/subfunctors, found general tools only.
   Mathlib Subfunctor.equalizer.forkIsLimit is a presheaf universal property; the
   short sectionwise proof here supplies it directly in the sheaf category.
4. PASS: the proof follows the original fibre-preservation route, then transports the
   given isomorphism and proves equivariance by subtype extensionality, map_add and
   unit naturality. The unit sk-prop-ext-invariance and its realized record are
   unchanged; no unit step is bypassed. All old proof_deps are accounted for above:
   torsor-h1 and algebraic-structures remain transitively needed, inverse-image-exact
   is unused and its private import is removed. Public imports remain appropriate
   for the original signatures; new proof-only imports are private.
5. PASS: compared the node proof steps, proof_deps unions and proof_origin with the
   actual Lean argument. The parent uses the proved fibre helper; the helper uses
   the lifting construction, algebraic comparison and Mathlib equalizer transport.
   The new node has its source, searches, creation, blueprint, chapter, unit and
   matching Lean record. Existing node fields outside stage-3 ownership are unchanged.

Second reading changed only this report: corrected the false assertion that the
exactness module was never imported, explicitly recorded its removed private import
and unused old proof dependency, and recorded the axiom and independent search checks.
The compiled Lean proofs and node records required no repair.
