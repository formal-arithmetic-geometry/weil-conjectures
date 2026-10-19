## Worker report

`lean/Sheaf/AlgebraicGeometry/ProperSurjectionEtaleSectionEqualizer.lean` states
`AlgebraicGeometry.Etale.properSurjectiveEtaleSectionEqualizer`, with one postponed
proof (`sorry`), no new definitions, no new nodes, and no statement correction.
The node's stage-1 proof and N7 review are preserved; N7 supplied a mathematical
split, not a Lean declaration. The earlier stale-assignment refusal therefore
does not justify treating a Lean statement as already delivered. The prescribed
stage-2 dry run now accepts this item.

The source was read in `literature/stacks-project/etale-cohomology.tex`,
`lemma-describe-pullback-pi-ph` (Tag 0DDW), including its entire equalizer argument,
and `lemma-proper-pushforward-stalk` (Tag 0A3T). The source argument works for all
sheaves of sets and hence for arbitrary abelian sheaves, without torsion. Its
last paragraph repeats first projection instead of saying second projection;
the node's explicit fibre-section contraction removes that expository typo.
The declaration docstring reproduces all eight steps of the node's proof.

Hypotheses and clauses, matched to Lean:

- Schemes U and V and their morphism p are `{U V : Scheme.{u}} (p : V ⟶ U)`.
- Properness is `[IsProper p]`. The recorded Mathlib class extends separated,
  universally closed and locally finite type; universal closedness implies
  quasi-compactness, so this is the node's finite-type properness convention.
- Surjectivity on underlying points is `[Surjective p]`; the class's field is
  exactly `Function.Surjective p` for the scheme's underlying point map.
- Arbitrary abelian small étale G is
  `G : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}`. There is no torsion,
  finite-generation, noetherianity, or invertibility assumption.
- Q is `pullback p p`, r₁ and r₂ are `pullback.fst p p` and `pullback.snd p p`,
  and q is `pullback.fst p p ≫ p`. They are canonical terms rather than
  extra quantified data. `pullback.condition` identifies r₂ followed by p
  with the same q used by r₁.
- Γ(U,G) is `G.obj.obj (op (Scheme.Etale.mk (𝟙 U)))`; the V section group
  is `((p)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj
  (op (Scheme.Etale.mk (𝟙 V)))`.
- Pullback of global sections is `pullSection p G` at the two identity étale
  objects and the morphism p. Its source definition first applies the
  inverse-image adjunction unit and then restricts along the canonical map
  V → U ×_U V. Thus it gives the required terminal-section unit map with
  its canonical identification, not an arbitrary arrow.
- `restrictAlong p G rᵢ q h` at identity étale objects is each parallel arrow.
  Its definition first applies the rᵢ adjunction unit, then the inverse-image
  composition isomorphism to q⁻¹G, then restricts to the terminal object Q.
  Both sides of the displayed equality have the same q⁻¹G section group.
- `Function.Injective (pullSection ...)` asserts uniqueness of descent.
  For every V-section σ', the equality of the two `restrictAlong` terms is
  equivalent to `∃ σ, pullSection ... σ = σ'`. This is existence precisely
  for compatible sections and also necessity. Together with injectivity it
  is the asserted equalizer of abelian groups: the section transports are
  additive (pullSection is the action of a composite of abelian-group
  morphisms, and restrictAlong is itself such a morphism).

Every variable and universe is explicit; the file also sets `autoImplicit false`.
All compatibility witnesses are equality proofs of the stated structural maps.
No hollow definition, arbitrary comparison, or auxiliary axiom was introduced.

Recorded statement dependencies and source declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme` and scheme morphisms.
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`.
- `def-weil-pbc-etale-sheaves`:
  `WeilConjectures.AlgebraicGeometry.EtaleSheaves`, the recorded abelian
  encoding `CategoryTheory.Sheaf ... AddCommGrpCat.{u+1}`. This record is
  explicitly mixed: its set-local-constancy predicate is not needed here.
  The module source was read with `scompile.py --source` because it is absent
  from the older local upstream checkout.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, and `.condition`.
- `def-weil-pbc-sites-and-cohomology`:
  `Sheaf.CategoryTheory.SiteCoveringAxioms` is imported as recorded. Its
  `CategoryTheory.Precoverage.IsSiteForCoverings` supplies the repaired
  general site convention; the record retains the existing sheaf and
  inverse-image APIs for its other clauses. The specialization used here is
  `WeilConjectures.AlgebraicGeometry.Sites.UpperStarSections`:
  `AlgebraicGeometry.Etale.pullSection`, `.restrictAlong`, `.transition`,
  `.upperStar`, `.upperStarLowerStarAdjunction`, and `.upperStarComp`.
  Their complete definitions and docstrings were read. No replacement
  notion is required.

The modules of recorded, stated proof dependencies are imported without `public`:
`WeilConjectures.SixFunctors.BaseChange.Square`,
`Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`,
`WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`,
`Sheaf.AlgebraicGeometry.ProperGeometricPointExchange`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`.
The direct-image definitions come transitively from the section-transport API;
properness permanence and fibre-product APIs are likewise already imported.
Unstated proof nodes remain obligations in the unchanged DAG.

Edge cases checked: empty U forces empty V and Q, with all section groups zero;
for p the identity, pullback is the identity and compatibility is automatic;
the zero sheaf gives singleton section groups; disconnected or nonreduced
proper fibres are allowed because the statement adds no connectedness or
reducedness hypothesis. No section of p itself, either over U or étale locally
over U, is assumed. The rational point used in the proof is only over each
nonempty algebraically closed geometric fibre.

Actual searches (the wrapper's `searches.jsonl` retains the returned records):

- `msearch.py ... leanfinder "For a proper surjective morphism of schemes and
  any abelian sheaf on the small etale site, global sections are the equalizer
  of pullback sections and the two projection pullbacks on the double fibre
  product"`: eight hits, including
  `CategoryTheory.regularTopology.mapToEqualizer_eq_comp` and affine-limit
  section formulas. None states this proper-surjection small-étale theorem.
- `msearch.py ... loogle 'IsProper, equalizer'` returned unknown identifier
  `IsProper`; that result was not used as evidence of absence. Retried with
  `loogle '"IsProper", "equalizer"'`, which returned zero hits without error.
- `msearch.py ... grep
  'proper.*(equaliz|descent)|equaliz.*proper|surjective.*etale.*sheaf'`:
  25 hits, chiefly condensed regular-topology equalizers, abstract equalizers,
  and flat descent. None is the statement here.
- `rg` of the exact node id and the proper/surjective/equalizer terminology in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, plus `rg` in the shared
  `lean/Sheaf` and side `lean/WeilConjectures`, found no existing exact theorem.
  `WeilConjectures.SixFunctors.Finite.Descent` has the abelian finite-surjective
  analogue, with `[IsFinite r]`, not arbitrary `[IsProper p]`; it cannot serve
  as an exact existing declaration. The `Sheaf` set-valued finite-surjective
  descent modules are likewise special cases. The generic regular-topology
  equalizer formula assumes its descent condition rather than proving this one.

Validation: all compilation uses the prescribed `scompile.py`; no direct Lean,
Lake, or global build was run. The final module and delivery are checked again
by `deliver2.py --no-push` before push. No statement fault or
`STATEMENT-DISPUTED` is present.

## Second reading by Q35

This is a second reading by the same dispatcher-started worker, as the brief
forbids starting other agents. It does not claim an independent second reader;
the maintainer's independent delivery review is still required.

With the node and signature open again, I checked that the sole morphism has
exactly properness and point-surjectivity, and that G is an unrestricted abelian
small-étale sheaf. The same canonical fibre product and common q occur on both
sides of the compatibility equation, including `pullback.condition` on the
second projection. The initial attempt evaluated the adjunction unit directly
at U; that gives sections over the base-changed terminal object, not literally
the terminal object V. I corrected this to the existing `pullSection` API,
which includes exactly the canonical terminal-object comparison. Injectivity
and compatibility iff membership in the image give all three equalizer
requirements, including uniqueness and the converse. The final statement has
no extra assumption and changes no node text.

I also expanded the docstring from a proof summary to all eight node steps,
used the AlgebraicGeometry topic directory, imported the recorded dependency
modules, checked explicit universes, and used the actual UTC date in the record.
