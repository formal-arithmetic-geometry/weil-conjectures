## What changed

Proved `AlgebraicGeometry.Scheme.exists_smooth_strict_local_field_coeff_data` in
`Sheaf.AlgebraicGeometry.SmoothStrictLocalFieldModelCoeffData`, with its statement unchanged.
The proof constructs the relative separable closure as the coefficient field, checks that the
core residue comparison is K-linear, obtains a finite separating family from finite-type stalk
and residue maps, transports separability to its image, and applies the existing proved
`Algebra.exists_section_of_separating_family`. The section equation identifies reduction with
the inverse residue comparison; the tower formula computes the transcendence degree.

Added the proof-only import `Sheaf.Paper.StrictHenselizationFunctoriality` to obtain henselianity
of the chosen strict-henselization ring. Updated the node's proof, proof dependencies and proof
origin to record this use. No definitions, signatures, public imports or consumers changed.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.Scheme.exists_smooth_strict_local_field_coeff_data`
(node `new-lem-sc-smooth-strict-local-field-model-coeff-data`). Added 0 holes; 0 remain in the
assigned module. No split-offs or new modules. This is a proof from existing declarations,
including the core and residue-functoriality obligations, rather than a claim that those
existing dependencies are now proved.

Single-file compilation passed without warnings. The separating-family argument also covers
the empty family (a = 0); no positive-dimensional or nonempty-family assumption is introduced.

## No longer needed

Removed redundant proof imports:
- `Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis` (already available through the
  separating-basis imports).
- `WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal` (the upstream instance
  alone does not provide the chosen coordinate-colimit ring's structure in the current source;
  use the existing residue-functoriality theorem for that ring).
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` (already public through smooth morphisms).
- `Mathlib.RingTheory.LocalRing.ResidueField.Ideal` (its needed instances are already
  available through the retained imports; checked by compilation without this import).

No mathematical proof-dependency nodes are pruned: the proof realizes the planned coefficient
field argument and uses all eight original dependencies. No unit statement or unit step is
bypassed. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node's original first step treated henselianity of the chosen ring as an immediate proved
upstream instance. The current source writes that ring as a chosen coordinate colimit, whereas
the upstream instance concerns its own strict-henselization ring. The existing
`AlgebraicGeometry.strictHenselizationResidue` states strict henselianity for exactly the chosen
ring, so the proof uses it with the canonical geometric residue embedding. This adds its
existing node `lem-weil-pbc-strict-henselization-functoriality` to the recorded proof dependencies.
No new mathematical assertion or repair is needed.

## Second reading by A3

1. Compared the sole delivered module and node with the repository versions. The complete
   existing theorem signature is byte-for-byte unchanged, as are its docstring and all public
   imports. The node changes only `proof`, `proof_deps` and `proof_origin`. There are no
   definition changes, new declarations, forced adaptations or change records. Verdict: pass.
2. Compiled the module through `lcompile.py` and checked the theorem with `#print axioms` in a
   scratch copy: only `propext`, `Classical.choice` and `Quot.sound`. There are no holes or
   forbidden declarations in the delivery. The field is the actual intermediate field
   `separableClosure k Ω`; the proof does not define data by choosing an arbitrary unproved
   existence witness. Verdict: pass against the compiled library.
3. No statements were split off or added. Read the section theorem's hypotheses: the proof
   supplies a surjective K-algebra map with maximal-ideal kernel, henselianity, algebraic
   independence and separability over the adjoined family. The family may be empty, so a=0
   introduces no exception. Searched the library for residue sections and coefficient fields
   and ran a differently worded Mathlib grep query through `msearch.py`; the other found
   residue-section results require adic completeness (one also characteristic zero), neither
   assumed here. Verdict: no duplicate or relabelled split.
4. Read the coefficient-field paragraph of
   `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-prop-sf-cbc/thm-sc-affine-torsion-cd.proof.md`
   and `dag/units/sk-prop-sf-cbc.json` (its `realized.statement` and `realized.steps` are empty).
   The proof retains the separating-basis/henselian-lifting route, using the existing general
   section theorem. Checked K-linearity using hK, he, hκ and hΩ, the finite-type residue-map
   composition, the transported separability, and the transcendence-degree tower calculation.
   All eight original dependencies remain used; the existing functoriality node supplies the
   additionally needed strict henselianity. No unit is bypassed or module withdrawn. Verdict:
   pass, with one additional redundant proof import removed.
5. Read the node and the Lean declarations or Mathlib matches of its nine dependencies. The
   four proof steps match the code: residue comparison and henselianity; finite separating
   basis; transport to E and section; residue bijectivity and transcendence degree. The
   `proof_deps` list is exactly the union of those steps' `uses`, and `proof_origin` names the
   source paragraph actually followed. Verdict: pass.

Changed in this reading: removed the redundant proof-only import
`Mathlib.RingTheory.LocalRing.ResidueField.Ideal` and the unnecessary local
`backward.isDefEq.respectTransparency` option. Independent removal probes compiled; the
retained `WeilConjectures.PointCount` import is necessary for `residueFieldAlgebraMap` and
`specMap_residueFieldAlgebraMap`. No proof argument, signature or node route needed repair.
