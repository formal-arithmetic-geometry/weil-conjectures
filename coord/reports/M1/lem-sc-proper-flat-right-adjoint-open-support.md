## Worker report

States `AlgebraicGeometry.proper_flat_rightAdjoint_open_support`, with only a `sorry`
proof, in `Sheaf.AlgebraicGeometry.ProperFlatRightAdjointOpenSupport`.
No definition is introduced, no node is corrected, and no dependency record is replaced.

Hypothesis and clause matching:
- Schemes X,Y: `{X Y : Scheme.{u}}`, without any nonemptiness assumption.
- Y quasi-compact and quasi-separated: `[CompactSpace Y] [QuasiSeparatedSpace Y]`.
- f:X→Y: `(f : X ⟶ Y)`.
- f proper: `[IsProper f]`, which includes quasi-compactness and separatedness.
- f flat: `[Flat f]`, equivalent to stalkwise flatness by `Flat.iff_flat_stalkMap`.
- f of finite presentation: `[LocallyOfFinitePresentation f]`, together with the
  quasi-compactness and quasi-separatedness already implied by properness. These
  three conditions are exactly the convention's Stacks 01TP finite presentation.
- Derived categories: explicit `HasDerivedCategory` binders for the shared module-sheaf
  carrier on X and Y, with independent hom universes wX,wY.
- Right adjoint on quasi-coherent derived categories: `a` has the exact functor type
  `schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X`; `adj : F ⊣ a`.
  `F` and `hF` specify the restriction of the recorded ambient `schemeDerivedDirectImage f`
  to the full quasi-coherent subcategories. The natural isomorphism says that forgetting
  quasi-coherence after F is the recorded direct image after forgetting quasi-coherence.
  This is a presentation of the node's Rf_* on D_QCoh, not an arbitrary unrelated
  left adjoint or an additional geometric hypothesis. No separate restriction definition
  is needed: Mathlib's full-subcategory inclusion and natural isomorphism express it.
- Every quasi-compact open V: `(V : Y.Opens) (hV : IsCompact (V : Set Y))`.
- U is its inverse image: the conclusion writes `f ⁻¹ᵁ V` directly.
- Q in D_QCoh(Y): `(Q : schemeDerivedQCohCategory Y)`.
- Support of Q in Y\V: `hQ` quantifies over every integer n and every y in V,
  asserting `Subsingleton` of the underlying cohomology stalk.
- Support of a(Q) in X\U: the conclusion quantifies over every integer n and every
  x in `f ⁻¹ᵁ V`, asserting the same cohomology-stalk vanishing for `(a.obj Q).obj`.
  This is the shared inline support encoding of SupportedPerfectGenerator and
  PseudoCoherentSupportAnnihilation, not a new support notion.

Dependencies read and used:
- def-weil-pbc-scheme-conventions is a convention record with no own declaration:
  its recorded Mathlib meanings are used as above.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `AlgebraicGeometry.IsProper`,
  with `IsSeparated` and `UniversallyClosed`; read their signatures/docstrings.
- Mathlib.AlgebraicGeometry.Morphisms.Flat: `AlgebraicGeometry.Flat`.
- Sheaf.AlgebraicGeometry.DerivedCategory: `AlgebraicGeometry.schemeDerivedCategory`,
  `schemeDerivedQCohProperty`, `schemeDerivedQCohCategory`; read all full definitions.
- Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage:
  `AlgebraicGeometry.schemeDerivedDirectImage`; read the ringed-space specialization
  and its K-injective-derived-functor construction.
- Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation provides the locally-finitely-
  presented predicate required by the convention.

Edge cases checked before writing: empty X or Y are permitted; V=empty gives
vacuous source and target vanishing conditions; V=Y asserts that a sends the zero
quasi-coherent derived object to zero, as an adjoint does. Q=zero is admitted.
No bounded-below hypothesis is imposed: the node's reviewed proof uses perfectness
of Rf_*P (0A1H with G=O_X[0]) and 0A9C(i), which allows arbitrary unbounded Q.
All cohomological degrees are integers, including negative degrees. No characteristic
or Noetherian restriction is imposed; a may be any choice of the specified right adjoint.

Source checked online: https://stacks.math.columbia.edu/tag/0E4G, Lemma 48.4.4(1).
The Stacks page states the bounded-below result; the reviewed DAG explicitly gives
its unbounded strengthening via 0A1H and 0A9C(i). This proof route is retained,
step by step, in the declaration docstring; there is no statement fault or dispute.

Searches for an existing statement (msearch.py, group M1, this item):
- leanfinder: "proper flat finitely presented scheme derived pushforward right adjoint
  preserves support outside quasi compact open": eight results, ordinary module
  pushforward adjunctions and ideal-sheaf support maps, no derived support theorem.
- loogle: "AlgebraicGeometry.IsProper, CategoryTheory.Adjunction": zero hits.
- leansearch: "derived direct image right adjoint preserves support proper flat scheme":
  unavailable, Internal Server Error; no mathematical verdict inferred.
- grep: "right.adjoint.*support|proper.flat|schemeDerivedQCoh", AlgebraicGeometry:
  zero Mathlib hits.
- rg on WeilConjectures with the same pattern, and grep for this blueprint id:
  no matches. rg on lean/Sheaf found existing derived carriers and inline support
  formulations, but no theorem asserting this right-adjoint support preservation.

Validation: the first single-file server compile passed cleanly in 2.5 seconds.
The deliver2.py --no-push compile and a repeated scompile then failed because the
server dependency artifact local/build/M1/Sheaf/AlgebraicGeometry/
SchemeDerivedDirectImage.olean does not exist. No dry-run OK was obtained, and
nothing was pushed. The independent second reading is left to the second worker.

## Dependency modules

- `def-pc-derived-direct-image`: the recorded `SchemeDerivedDirectImage` declaration is the exact notion required, but its object file is absent from the server's last-green build. The included module states the dependency exactly and is compiled together with this item; the node `lean.note` records this reason.

## Second reading by M1

I reread the node statement, its Stacks source, the dependency records, and both delivery
modules independently. The item list and verdicts are:

- `Y : Scheme.{uT}` with `[CompactSpace Y] [QuasiSeparatedSpace Y]`: rendered by the
  implicit scheme binders and instances; this is exactly quasi-compact and
  quasi-separated Y.
- `f : X ⟶ Y` with `[IsProper f] [Flat f]
  [LocallyOfFinitePresentation f]`: rendered by the explicit morphism and classes. The
  Mathlib `IsProper` class supplies separated, universally closed, and locally finite type;
  universally closed supplies quasi-compactness, so this matches properness and the source's
  required quasi-compact/quasi-separated morphism context. The finite-presentation class is
  the stated finite-presentation hypothesis.
- The two derived-category instances are explicit shared
  `HasDerivedCategory` binders with independent homological universes; they are the carrier
  instances used by `schemeDerivedQCohCategory` and do not add a geometric hypothesis.
- `F` and `hF` render a functor on the quasi-coherent derived full subcategories and a
  natural isomorphism from its ambient inclusion composite to
  `schemeDerivedDirectImage f` after inclusion. This is the node's restricted `Rf_*`.
- `a` and `adj : F ⊣ a` render the specified right adjoint, with no extra property of `a`.
- `V : Y.Opens` and `hV : IsCompact (V : Set Y)` render a quasi-compact open; `f ⁻¹ᵁ V`
  is the inverse-image open U.
- `Q : schemeDerivedQCohCategory Y` and `hQ` render Q supported on `Y \ V`: for every
  integer degree and every point of V, the stalk of the homology sheaf is `Subsingleton`.
- The conclusion quantifies over every integer and every x in U and gives the same stalk
  `Subsingleton` condition for every homology sheaf of `a.obj Q`, exactly support on
  `X \ U`.

No mismatch was found and no statement change was needed. In particular, the quantifier
order, all integer degrees (including negative degrees), and the absence of a bounded-below
condition agree with the reviewed node proof's unbounded strengthening. The source is Stacks
Tag 0E4G, Lemma 48.4.4(1), whose proof uses perfect tests, proper-flat direct-image
perfectness, support annihilation, and projection formula; the declaration docstring records
those steps and all cited proof nodes.

Edge cases checked: `V = ∅` makes both support hypotheses/conclusions vacuous; `V = ⊤`
reduces the premise to vanishing of Q and the conclusion to vanishing of its right-adjoint
image; `Q = 0` is admitted; empty schemes and all integer degrees are admitted; no
characteristic, Noetherian, or universe restriction beyond the shared scheme universe and
explicit derived-category hom universes is introduced.

Existing-definition searches were repeated with the project search tools: LeanFinder query
`proper flat right adjoint derived support`, Loogle query `IsProper Adjunction support`,
`msearch.py` query `proper flat finitely presented scheme derived pushforward right adjoint
preserves support`, and ripgrep for `proper_flat_rightAdjoint_open_support`,
`rightAdjoint.*support`, and `schemeDerivedQCoh` in Mathlib, WeilConjectures, and
`lean/Sheaf`. They found only generic adjunction/support declarations and the recorded
`schemeDerivedDirectImage`; no existing theorem states this item. The dependency declaration
`AlgebraicGeometry.schemeDerivedDirectImage` was read in full and is exact. Its object file is
absent from the last-green server artifact, so the delivery retains the dependency module and
node note and compiles it together with this theorem.

The combined `scompile.py` check passes for
`SchemeDerivedDirectImage.lean` followed by
`ProperFlatRightAdjointOpenSupport.lean`, with only the intended theorem `sorry`.
