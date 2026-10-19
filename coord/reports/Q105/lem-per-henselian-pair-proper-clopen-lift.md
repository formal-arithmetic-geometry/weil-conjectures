## Worker report

Stage 2 for `lem-per-henselian-pair-proper-clopen-lift`, group Q105.
The module `Sheaf.AlgebraicGeometry.HenselianPairProperClopenLift` states
`AlgebraicGeometry.Scheme.exists_proper_clopen_lift_of_henselianPair` with `sorry`.
It introduces no definition and proves nothing. The natural statement, statement
dependencies, proof and proof dependencies are unchanged. Only `lean` is added to
the copied node. Q68's existing report and review concern stage 1; the node had no
Lean record when this stage-2 work began. The previous worker's claim that Q68 had
already completed this stage was therefore not a reason to omit the Lean statement.

Source read: Stacks Project, `more-morphisms.tex`, Tag 0CT9,
`lemma-split-off-proper-part-henselian`, including all three proof reductions.
The node's statement agrees with this source. The theorem docstring carries all
five steps of the current DAG proof, which uses Nagata in place of the source's
preliminary Chow reduction.

Hypothesis and clause correspondence:

- A commutative ring is `{A : Type u} [CommRing A]`, and its ideal is `(I : Ideal A)`.
- The henselian-pair hypothesis is `[HenselianRing A I]`, exactly the recorded
  henselian-terminology interface. The node's idempotent formulation is equivalent
  to Mathlib's root-lifting definition, as explained in that dependency's record.
  No local, nonzero, Noetherian, complete or adic assumption is imposed.
- The scheme and its structure morphism are `{X : Scheme.{u}}`
  and `(f : X ⟶ Spec (.of A))`.
- Separatedness is `[IsSeparated f]`; finite type is the conjunction encoded by
  `[LocallyOfFiniteType f] [QuasiCompact f]`, as the finite-type dependency records.
- The quotient closed subscheme is `Spec (.of (A ⧸ I))`, mapped to `Spec (.of A)`
  by `Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))`.
- The closed fibre is the chosen `pullback f` of this quotient spectrum map.
  This is precisely the scheme-base-change convention recorded in
  `def-pc-base-change`; its first projection goes to `X`, its second to the quotient
  spectrum. No alternative base-change construction is introduced.
- The given open subscheme is `Y : (pullback f ...).Opens`. Its closedness is
  `hY : IsClosed (Y : Set (pullback f ... : Scheme.{u}))`. Openness is part of the
  type `Scheme.Opens`, not an omitted condition.
- The properness of `Y` over `Spec (A/I)` is the explicit instance
  `[IsProper (Y.ι ≫ pullback.snd f ...)]`. This is the restriction of the specified
  fibre structure map, not an arbitrary proper map out of `Y`.
- The desired open subscheme is the existential `∃ W : X.Opens`.
  Its closedness is `IsClosed (W : Set X)`, and its properness over the original
  base is `IsProper (W.ι ≫ f)`.
- The fibre equality is `(pullback.fst f ...) ⁻¹ᵁ W = Y`, equality in the opens of
  the closed fibre. This asserts equality of open subschemes, not just isomorphism
  of abstract schemes. Mathlib's `Scheme.Opens.toScheme` is restriction of the
  ambient scheme, and `Scheme.Opens.ι` its canonical inclusion.
  `AlgebraicGeometry.pullbackRestrictIsoRestrict` in
  `Mathlib.AlgebraicGeometry.Restrict` identifies the inverse-image open with the
  base-changed open subscheme, compatibly with its inclusion. Pullback pasting
  identifies this with `W ×_Spec(A) Spec(A/I)`. Equal opens have the same restricted
  structure sheaf, as required by the node's final sentence.
- The explicit universe `u` is arbitrary and shared by the ring and schemes, as
  in Mathlib's category of schemes and its fibre products. There is no separate
  smaller testing universe and no nonemptiness assumption.

Dependency interfaces read and used:

- `def-weil-pbc-henselian-terminology`: imported
  `WeilConjectures.Mathlib.RingTheory.Henselian`; its recorded bundle includes
  Mathlib's `HenselianRing`. Read both that upstream module and the full Mathlib
  class signature and docstring. Strict henselianity is not used by this node.
- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`, from
  `Mathlib.AlgebraicGeometry.Scheme`; the full structure definitions were read.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, from the
  same Mathlib module; the definitions and docstrings were read.
- `def-weil-proper-morphism`: `AlgebraicGeometry.IsProper`, `IsSeparated` and
  `UniversallyClosed`, from `Mathlib.AlgebraicGeometry.Morphisms.Proper` and its
  dependencies. Properness includes quasi-compactness through universal closedness,
  so Mathlib's locally-of-finite-type formulation has the node's meaning.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`, from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, and `AlgebraicGeometry.QuasiCompact`,
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`; the full classes were read.
- `def-pc-base-change`: imported its recorded module
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; read its current source
  through `scompile.py --source`. Its module docstring expressly uses `pullback`,
  `pullback.fst` and `pullback.snd` for scheme base change. Its main recorded
  `Scheme.Modules.moduleBaseChange` concerns modules and is not substituted for a
  scheme fibre product here.

Proof imports retain the modules for the already stated proof inputs:
`WeilConjectures.Compactification.Defs` (`Compactification`, `HasCompactification`),
`WeilConjectures.Compactification.NagataCompactification` (`NagataCompactification`),
`Sheaf.AlgebraicGeometry.HenselianClopenRestriction`
(`Scheme.henselian_clopen_restriction`),
`WeilConjectures.AlgebraicGeometry.HenselianConnectedness`
(`Scheme.Hom.spectralSpace_and_isClosed_and_isConnected_inter`), and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper`.
Mathlib's properness, quasi-compactness, quasi-separatedness and open-immersion
modules provide the other recorded proof tools. No unstated proof dependency has
been restated, and none is needed to formulate this theorem.

Edge cases checked before writing:

- Empty `Y`: the empty open in `X` is an allowed witness, with its proper empty
  structure morphism and the required empty inverse image.
- `I = 0`: the closed fibre is canonically `X`, so a prescribed proper clopen
  already gives the required lift.
- The zero ring and empty `X`: all relevant schemes over the empty spectrum are
  empty. No `Nontrivial A` or nonempty carrier assumption excludes them.
- Proper `X`: the statement includes this case and reduces to the proper clopen
  restriction theorem; properness is not assumed for general `X`.
- For `A = k[[t]]`, `I = (t)`, and
  `X = Spec(k[[t]]) ⨿ Spec(k((t)))`, the second component has empty closed fibre
  and is nonproper. The first component is the lift of the whole closed fibre.
  The theorem requests a proper `W`, and does not incorrectly require `W = X`.
- `I = ⊤` can be henselian only for the zero ring, since the henselian-pair
  interface requires containment in the Jacobson radical. It does not create a
  missing nontrivial-ring case.

Existing-declaration searches made through `msearch.py`:

- LeanFinder: “Over a henselian pair every proper clopen subscheme of the closed
  fibre of a separated finite type scheme lifts to a proper clopen subscheme”.
  Eight hits, including `Algebra.QuasiFiniteAt.isClopen_singleton`, `HenselianRing`,
  `HenselianLocalRing`, and affine-limit existence lemmas; no matching theorem.
- Loogle: `AlgebraicGeometry.IsProper, HenselianRing`; zero hits.
- Mathlib grep: `henselian|proper.*clopen|clopen.*proper` in `AlgebraicGeometry`;
  zero hits.
- LeanSearch: “henselian pair lifting proper open and closed subscheme of special
  fibre of separated finite type scheme”. Eight hits, consisting of henselian-local
  ring declarations and `AlgebraicGeometry.isProper_eq`; no matching theorem.
- Upstream `WeilConjectures` source grep for the item id returned no match.
  Searches for henselian/clopen/proper combinations found no lift theorem.
- Project `lean/Sheaf` searches found `Scheme.henselian_clopen_restriction`,
  whose ambient morphism is proper, and the item's citation in
  `ElkikFiniteEtaleAwayCompletion`. Neither states this separated finite-type
  ambient result. The chosen new declaration name had no existing source match.

Validation: `scompile.py Q105 lem-per-henselian-pair-proper-clopen-lift` compiled the
module cleanly in both its sandbox view and its actual module path, 1.9 seconds
each. An initial elaboration ambiguity inside `Set (pullback ...)` was repaired
with the explicit `Scheme.{u}` annotation; it did not change the statement.
The final packet is additionally checked by the prescribed delivery dry run.
No statement dispute, statement correction, new node or dependency repair is needed.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
