## What changed

Proved `AlgebraicGeometry.Scheme.picard_affine_projective_base_change`, with its
statement unchanged. Added the proved module
`Sheaf.AlgebraicGeometry.PicardAffineStructureModelTransport`, which isolates the
localized-to-spectrum representation comparison without flatness or K-flatness.
The main proof uses the existing affine K-flat pullback comparison and canonical
flat-invertible derived base change. Both iterated pullback squares and the
structure-module identifications are proved explicitly.

The transport proof derives the sectionwise open-square comparison already proved
in `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections` using exact
open restriction and K-injective preservation. It uses `import all` for that proved
private comparison, as the existing `NestedOpenSingleDirectImageComparison` does.
The exact affine equivalences cancel by their actual counits and restriction
composition isomorphisms; no arbitrary transport equivalence is chosen.

Both modules compile together in import order through `lcompile.py`, without
warnings. Edge cases checked in the argument: empty affine open, zero coordinate
ring, empty fibre product, zero coefficient, and unbounded P. All comparisons are
functorial identities or isomorphisms and require no nonempty point, nonzero ring,
boundedness, finite generation, or additional flatness hypothesis.

Sources checked: [Stacks 08FE](https://stacks.math.columbia.edu/tag/08FE),
[06Z0](https://stacks.math.columbia.edu/tag/06Z0), and
[0A1D](https://stacks.math.columbia.edu/tag/0A1D).

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.picard_affine_projective_base_change`
(node `lem-sc-picard-affine-projective-base-change`).

Also proved the new theorem
`AlgebraicGeometry.Scheme.picard_affine_structure_model_transport`
(node `lem-sc-picard-affine-structure-model-transport`).

No `sorry` remains in either delivered module; no holes were added and none were
split off. This closes one hole using existing library declarations; it does not
claim that all transitive dependencies are axiom-free. The delivery's axiom probe
checks for forbidden axioms, allowing the existing dependencies' `sorryAx` as the
stage-3 process prescribes.

## No longer needed

No original public import was removed; each is retained for the original interface.
The new transport module needs neither scalar extension nor total tensor products,
so its initial copied imports of `Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`,
`Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic`, and
`Mathlib.Algebra.Homology.BifunctorShift` were removed.

Two planned direct dependencies are replaced:

- `lem-pc-affine-localized-site-derived-transport`, module
  `Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport`: the exact
  functors in affinePerfectSheafification cancel explicitly instead.
- `lem-pc-restrict-derived-direct-image-open`, module
  `Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`: use the proved
  sectionwise open-square comparison and derive it directly for the supplied
  cartesian square, avoiding transport through an inverse-image-open presentation.

`lem-pc-flat-module-canonical-derived-pullback`, module
`Sheaf.AlgebraicGeometry.FlatModuleCanonicalDerivedPullback`, is no longer a direct
proof dependency: the proved canonical single-pullback comparison packages that
step. It remains a transitive dependency, so no closure pruning is claimed for it.
`def-pc-tensor-pullback-composition-iso`, module
`Sheaf.AlgebraicGeometry.TensorPullbackCompositionIso`, is no longer a direct
dependency of the main theorem but remains needed in the new transport theorem.
The tensor-pullback adjunction is explicitly recorded as a proof dependency in
both nodes.
The two replaced modules may remain reachable elsewhere; this report claims only
that this proof does not import or use them directly. No unit route is bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The planned affine localized-site transport
lemma supplies an existential equivalence together with a tilde comparison but
does not characterize that equivalence on arbitrary derived direct images. That
interface alone is insufficient for the proposed geometric transport. The proof
uses the concrete restriction and over-equivalence functors instead. The original
three mathematical steps are preserved, with the first now proved in its own module.

## New nodes

`lem-sc-picard-affine-structure-model-transport` states and proves only the first
step: transport of the supplied localized model to the spectrum, before any scalar
extension. It has no flatness, quasi-compactness, separatedness or K-flatness
hypothesis and no base-change ring B. It is strictly a part of the original
argument and has a complete Lean proof. Its dependencies and the original node's
updated proof dependencies follow the delivered proof. No change records or
forced adaptations are needed; no existing signature or definition changed.

## Second reading by J3

1. Compared the complete original module with the delivered version and checked
the existing theorem signature byte for byte. Pass: no hypothesis, conclusion,
definition, existing docstring or public interface changed. Only proof bodies,
private proved helpers and proof imports were added. The existing node changes
only proof, proof_deps and proof_origin.

2. Read both proofs and compiled both files in import order through lcompile.py.
Pass: no warnings, errors, local sorry, axiom, unsafe, opaque, implemented_by,
extern or hollow definition. The only classical choice in the new argument
chooses a tensor-pullback adjunction to use leftAdjointUniq; its left adjoint is
fixed and the comparison is characterized by the adjunction, rather than an
arbitrary existence witness. The supplied representation and trivialization are
eliminated in theorem proofs, not used to define data. A scratch-copy axiom check
is recorded below.

3. No statements were split off with sorry. The new proved transport theorem
is strictly the affine/open-transport part of the argument: it has no B, ring
map, K-flatness or flat-family assumptions. Pass after checking empty opens,
zero rings, empty pullbacks and unbounded complexes: every step is an exact
restriction comparison or actual isomorphism, with no choice of points.
Independent leanfinder search for exact open-square derived pushforward,
loogle search for restrictFunctorComp, msearch grep with restriction/derived
keywords, and rg of the existing library found generic restriction identities
and the existing nested-open comparison, not this supplied-localized-model
transport statement. Its node and full docstring proof are present.

4. Pass: the proof uses the shortest available affine K-flat and canonical
flat-invertible comparisons; the new lemma cancels the concrete affine functors
instead of choosing the existential transport equivalence. Checked the old
proof_deps against the revised route; all removed direct dependencies are listed
in No longer needed, including composition and canonical flat pullback that
remain transitive. All retained original public imports support the original
statement. In the new module, TensorPullback is public and its adjunction is a
plain proof import. Read dag/units/sk-prop-av-cube.json: its realized arrays are
currently empty; this delivery neither changes them nor bypasses a unit step.
The chapter/unit cube route remains unchanged.

5. Pass after repair: both nodes' steps and proof_deps follow the actual Lean
proof, including the tensor-pullback adjunction used for leftAdjointUniq.
Checked the new node's statement, Lean signature, source, three searches,
blueprint provenance, chapter/unit, created fields and proof_origin.

Changes made in this second reading: restored the exact signature whitespace;
replaced the new module's public adjunction import by public TensorPullback and
a plain adjunction import; recorded adjunction dependencies in both nodes;
made the old composition dependency's indirect use explicit in the report.
No mathematical proof rewrite or new hole was needed.

Scratch-copy #print axioms results: picard_affine_structure_model_transport
uses only propext, Classical.choice and Quot.sound;
picard_affine_projective_base_change uses those three and existing sorryAx.
The original hole is closed and zero holes are added; this is not a claim of
axiom-free completion of its still-open transitive dependencies.
