## Worker report

The delivery states `AlgebraicGeometry.lci_etale_pointwise_invariance` in
`Sheaf.AlgebraicGeometry.LciEtalePointwiseInvariance`. It has one theorem, whose proof
is `sorry`, and no new definitions, auxiliary theorems, or axioms. The mathematical
statement and accepted stage-1 split are unchanged. The node gains only its Lean record
and the already landed definition node `def-trf-complete-intersection-local-algebra`
in `stmt_deps`, as authorized by brief-stage2 §5.

### Stage handoff

The inherited BLOCKED ending concerned the Q97 stage-1 split. The live node has
`reviewed` PASS but no `lean` or `reviewed_lean` record; the queue lists it at stage 2.
There is no released repair note. This delivery formalizes that accepted split and
therefore does not re-split the reviewed item (brief-stage2 §0, stage handoff).
The prescribed CompactObject example is now a withdrawn module with no declarations;
the module header instead follows the current module-mode convention and the recorded
LciPointwiseCriterion module.

### Hypothesis and conclusion audit

- A field k: `(k : Type u) [Field k]`; Field is Mathlib's nontrivial commutative field.
- Schemes Y and Z: `(Y Z : Scheme.{u})`, with their given maps
  `(sY : Y ⟶ Spec (.of k)) (sZ : Z ⟶ Spec (.of k))`. Explicit maps are appropriate
  because two schemes over the same field and their compatibility are involved.
- Both schemes locally of finite type over k:
  `[LocallyOfFiniteType sY] [LocallyOfFiniteType sZ]`. There is no finite-type or
  quasi-compact assumption on the entire schemes.
- The étale k-morphism: `(e : Z ⟶ Y) [Etale e] (_he : e ≫ sY = sZ)`.
  The equality is exactly the condition that e is over k; it is not omitted.
- Every point z: `(z : Z)`. The corresponding point y is written directly as `e z`.
- The left local ring is `Z.presheaf.stalk z`; the right local ring is
  `Y.presheaf.stalk (e z)`.
- The iff is precisely between `Algebra.IsCompleteIntersectionLocalAlgebra k`
  applied to these two stalks. In each case the explicit Algebra argument is the
  ring map from k to the stalk obtained by `Scheme.ΓSpecIso`, the structure morphism's
  `appLE ⊤ ⊤ le_top`, and the germ at the point, followed by `hom.toAlgebra`.
  Thus the field actions are the given structural ones, not arbitrary actions.
- The local-ring meaning fixed by `lem-trf-lci-pointwise-criterion` is retained:
  the imported predicate from `def-trf-complete-intersection-local-algebra` asks for
  a regular local k-algebra R essentially of finite type, a finite regular sequence
  in its maximal ideal, and a k-algebra isomorphism from the quotient to the stalk.
  `IsRegularLocalRing` itself supplies locality and Noetherianity. The list ideal
  `Ideal.ofList` and the range ideal used in the criterion generate the same ideal.
  The predicate also records that the target is local and essentially of finite type;
  these are automatic for the stalks of the locally finite type k-schemes here.
  Properness of the presentation ideal follows from the nonzero local target; regularity
  then places its entries in the maximal ideal, as explained in the criterion docstring.
- No surjectivity, quasi-compactness, separation, or perfection hypothesis occurs.
  No nonemptiness hypothesis occurs. Only the stated iff is concluded.

### Dependencies used

Statement imports and recorded declarations read in full:

- `Mathlib.Algebra.Field.Defs`: `Field` (available through the other public imports).
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.TraceFormula.LciPointwiseCriterion`:
  `AlgebraicGeometry.lci_pointwise_criterion`. Its clause (3), including the exact
  structure-map/germ field action, fixes the local-ring interpretation used here.
- `Sheaf.RingTheory.CompleteIntersectionLocalAlgebra`:
  `Algebra.IsCompleteIntersectionLocalAlgebra`, the existing definition used on both
  stalks. Its node is added to the item's statement dependencies; it is not copied
  or repaired in this delivery.

The stated proof dependencies are imported without `public`:
`Mathlib.RingTheory.Flat.Basic` (`Module.Flat.of_free`),
`Mathlib.LinearAlgebra.Basis.VectorSpace` (`Module.Free.of_divisionRing`),
`Mathlib.AlgebraicGeometry.Morphisms.Flat` (`AlgebraicGeometry.Flat`),
`Mathlib.AlgebraicGeometry.Noetherian` (`AlgebraicGeometry.IsLocallyNoetherian` and
`LocallyOfFinitePresentation.iff_locallyOfFiniteType`),
`Mathlib.AlgebraicGeometry.Fiber` (`Scheme.Hom.fiber`),
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` (`Scheme.Hom.isOpenMap`), and
`Sheaf.TraceFormula.SyntomicLocusBaseChange` (`syntomic_locus_base_change`).
The already public Etale module also supplies `Etale.etale_comp`, `Etale.of_comp`,
and the open-immersion instance. The proof-only node
`lem-sfb-syntomic-etale-source-locality` currently has no Lean record or Mathlib match;
there is therefore no module for that proof dependency to import yet. It is named in
the complete proof docstring for later stage-3 work and is not needed to state the iff.

### Source and edge cases

Read Stacks `descent.tex`, lemma-syntomic-syntomic-local-source (036S), and
`morphisms.tex`, lemma-syntomic-locally-standard-syntomic (01UE) and
lemma-set-points-where-fibres-lci (02V3). Over the field, the structural maps are flat
and locally finitely presented. Their maximal syntomic source opens are exactly the
CI local-ring loci. Étale ascent on the preimage gives one implication, and descent
from the source locus to its open image gives the other. This is the node's four-step
proof, recorded with all dependency ids in the theorem docstring.

Checked the empty source: there is no z to instantiate, hence the assertion is vacuous.
An empty target admits no map from a nonempty source, so it introduces no missing case.
An open immersion with proper image tests only the points in its image; no surjectivity
is needed. The identity case is the identical stalk condition with the same scalars.
An empty regular sequence is allowed, covering regular local presentations. Fields
of arbitrary characteristic and imperfect fields are included. No finite total cover,
separation condition, or restriction to closed points occurs. The field, schemes and
stalks use a common arbitrary universe, as in the recorded criterion; any smaller
field or scheme can be lifted to a common universe. The presenting ring in the
existing predicate lives in the maximum universe, so it is not too small.

### Searches

All remote searches used the prescribed `msearch.py Q27` wrapper for this item.

- LeanFinder: “An etale morphism of schemes locally of finite type over a field preserves
  and reflects the complete intersection property of the local rings at corresponding
  points”. Eight hits, including `RingHom.Etale.propertyIsLocal`, `Etale.of_comp`,
  and `Algebra.mem_etaleLocus_iff`; none states CI local-ring invariance.
- Loogle: `"Etale", "CompleteIntersection"`. Zero hits.
- Mathlib grep, AlgebraicGeometry:
  `((etale|Etale).*(CompleteIntersection|lci))|((CompleteIntersection|lci).*(etale|Etale))`.
  Zero hits.
- LeanSearch: “Etale maps between schemes over a field preserve and reflect complete
  intersection local rings”. Eight hits for étale definitions, formal étaleness,
  smoothness and localization stability; none states the item.
- Source `rg` in `lean/WeilConjectures` and `lean/Sheaf` for `CompleteIntersection`,
  `lci_pointwise`, `lci.*etale`, `etale.*lci`, and the item id. Found the pointwise
  criterion and existing CI definitions, including the reused local-algebra definition;
  found no étale pointwise invariance theorem. The exact proposed declaration name
  was also absent from both libraries, Mathlib, and `dag/lean_names_upstream.json`.
- DAG search for `CompleteIntersectionLocalAlgebra` found
  `def-trf-complete-intersection-local-algebra`, which is reused, not recreated.

### Validation

`scompile.py Q27 lem-sfb-lci-etale-pointwise-invariance` compiled the delivered file
in both its private sandbox and its library module position: clean, 1.4 s and 1.5 s.
Every universe and variable is bound explicitly, `autoImplicit` is false, and all
lines are at most 100 characters. The only postponed proof is the item's theorem.
No statement correction, disputed statement, new node, or dependency repair is needed.

## Second reading by Q27

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
