## Worker report

Item: lem-sc-p1-ext-coherent-dim-one-vanishing. The module
`Sheaf.AlgebraicGeometry.CoherentExtVanishing` states both clauses of the node with
`sorry` proofs: the general regular Noetherian finite-dimensional case and the explicit
projective-line case. No new definition, new node, dependency replacement, or statement
correction was needed. Only the item's `lean` record changes.

Source checked: [Stacks Tag 0FZ3, Lemma 57.9.4 (1)](https://stacks.math.columbia.edu/tag/0FZ3).
The local literature file `literature/stacks-project/equiv.tex` was absent, so the tag was
opened online. Its hypotheses and conclusion agree with the node's general assertion.
The module docstrings carry the five steps of the node's proof, including each named input.

Hypotheses and clauses, individually:

- A scheme X: `(X : Scheme.{u})`, with `u` explicitly declared and unrestricted.
- Regular: `hregular : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U)`.
  This is the defining affine-neighbourhood condition from the regular-scheme node's
  `mathlib_match.how` and `lean.note`; `U.1` is the underlying open. No stalkwise
  equivalence is assumed or defined privately. `IsRegularRing` includes Noetherianity
  of each such coordinate ring and regularity of every prime localization.
- Quasi-compact: `[CompactSpace X]`, exactly the recorded specialization of the
  quasi-compact-scheme dependency, with no separation requirement.
- Locally Noetherian: `[IsLocallyNoetherian X]`. Together with compactness this is
  precisely the node's Noetherian-scheme hypothesis.
- Finite dimension d: `(d : ℕ) (hdim : X.dim = (d : WithBot ℕ∞))` uses the recorded
  supremum-of-local-ring-dimensions definition, not an unbridged topological dimension.
- O_X-modules F and G: `(F G : X.Modules)`.
- F coherent: `hF : RingedSpace.IsCoherent X.toRingedSpace F`.
- G coherent: `hG : RingedSpace.IsCoherent X.toRingedSpace G`.
  The recorded predicate checks finite type and finite-type kernels of every map from
  finite free modules on every open. `X.Modules` unfolds to the same module-sheaf
  carrier as this predicate (confirmed by the server's successful elaboration).
- Ext as in def-sc-ext-sheaf: `Scheme.Modules.Ext F G i`, the existing abbreviation for
  `Abelian.Ext` on the full abelian category of all O_X-modules. It is not Ext computed
  inside the category of coherent modules. `[HasExt.{u} X.Modules]` is precisely the
  existing abbreviation's size infrastructure, available for this Grothendieck abelian
  category, not a new geometric assumption or projective-resolution assumption.
- For every i > d: `(i : ℕ) (hi : d < i)`.
- Ext^i = 0: `Subsingleton (Ext F G i)`. This is equivalent to triviality of its additive
  group, since the Ext type has zero; it does not mean vanishing of the sheaf Ext alone.
- In particular, X = P^1_k: a separate theorem uses
  `ProjectiveLine (Spec (CommRingCat.of k))`, the existing projective line used by the
  standard-cover dependency, which is projective space on `ULift (Fin 2)` over Spec k.
- k any field: `(k : Type u) [Field k]`, with no characteristic restriction.
- Both coherent modules in that clause: F and G belong to that projective line's
  `.Modules`, and `hF`, `hG` apply the same recorded coherence predicate there.
- For all i >= 2: `(i : ℕ) (hi : 2 ≤ i)`.
- Vanishing in that clause: `Subsingleton (Ext F G i)`, without asking the caller to
  supply regularity, compactness, local Noetherianity or dimension-one proofs for P^1.
  Its `HasExt` binder is the same existing size infrastructure as above.

Dependency declarations read and used:

- def-weil-regular-scheme: `Mathlib.RingTheory.RegularLocalRing.Defs`, `IsRegularRing`
  and `IsRegularLocalRing`; read their full class signatures/docstrings and the node's
  recorded affine-neighbourhood specialization.
- def-weil-pbc-quasi-compact-scheme: `Mathlib.Topology.Defs.Filter`, `CompactSpace`
  and `IsCompact`; read the compactness class/docstring. The dependency is a Mathlib
  leaf and therefore needs no `lean` record.
- pqf-def-locnoeth: `Mathlib.AlgebraicGeometry.Noetherian`,
  `AlgebraicGeometry.IsLocallyNoetherian`; read its coordinate-ring class signature.
- def-pc-dimension: `Sheaf.AlgebraicGeometry.Dimension`,
  `AlgebraicGeometry.Scheme.dim`; read its complete definition/docstring, including
  the empty-scheme convention.
- pqf-def-coherent: `Sheaf.AlgebraicGeometry.Coherent`,
  `AlgebraicGeometry.RingedSpace.IsCoherent`; read the full predicate and docstring.
- def-sc-ext-sheaf: `WeilConjectures.AlgebraicGeometry.Modules.Ext`,
  `AlgebraicGeometry.Scheme.Modules.Ext`; read its full abbreviation signature,
  surrounding HasExt binder and docstring. The upstream text mistakenly describes
  contravariant derived Hom, but its actual abbreviation is the correct classical
  categorical Ext, as the corrected dependency node says.
- def-sc-p1-standard: `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits`,
  `AlgebraicGeometry.ProjectiveLine.TwistData`; read all fields and docstring. Only its
  underlying existing `AlgebraicGeometry.ProjectiveLine` is needed here; twisting
  generators are irrelevant to Ext vanishing. Read that abbreviation in
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` as well. No duplicate P^1 is made.

Edge cases checked before writing: d = 0 gives vanishing only for positive i, as expected
for a zero-dimensional regular Noetherian scheme. i = d and i = 0 are not incorrectly
claimed to vanish. Empty X has dim = bottom, so cannot satisfy equality to any natural d;
this is consistent with the node's finite-dimensional premise and the dimension node's
nonempty convention, and Ext on an empty scheme is trivial anyway. F = 0 or G = 0 poses
no issue. The projective-line clause includes i = 2, arbitrary field characteristic and
arbitrary universe u. Regularity and coherence impose substantive conditions; no
vacuous scheme-map hypothesis appears. The independently landed
`ProjectiveLine.noetherian_regular_dim_one` was also read to check the precise P^1 carrier
and regularity/dimension form to be used in stage 3.

Searches on 2026-10-11:

- msearch.py leanfinder: "Higher Ext groups of coherent modules on a regular Noetherian
  scheme vanish above its dimension". Eight hits, including
  `HasProjectiveDimensionLT.subsingleton` and `HasInjectiveDimensionLT.subsingleton`;
  these require abstract dimension bounds and do not state the regular-scheme theorem.
- msearch.py loogle: "CategoryTheory.HasProjectiveDimensionLT.subsingleton,
  AlgebraicGeometry.Scheme.Modules.Ext". Zero hits; the service does not index the
  upstream Scheme.Modules.Ext name (reported unknown identifier).
- msearch.py grep: "coherent.*Ext|Ext.*regular|Ext.*dimension", subdirectory
  AlgebraicGeometry. One unrelated etale/smooth relative-dimension hit; no match.
- msearch.py leansearch: "Ext groups of coherent sheaves on a regular Noetherian scheme
  vanish above the dimension". Service unavailable, Internal Server Error; no verdict
  inferred from that failure.
- rg of the source WeilConjectures tree and lean/Sheaf for
  `regular.*[Ee]xt|[Ee]xt.*[Cc]oherent|lem-sc-p1-ext-coherent-dim-one-vanishing`:
  only unrelated extension/hom-ext occurrences and regular-local Ext vanishing, not this
  scheme-theoretic statement. The regular-local theorem is a distinct proof dependency.
- grep -rn of the exact item id in the upstream WeilConjectures tree: no hit.
- rg of dag/lean_names_upstream.json for `coherent.*[Ee]xt|[Ee]xt.*coherent|[Ee]xt.*regular`:
  no hit. The chosen new declaration names were also absent from the source/project
  searches and are checked against all upstream/Mathlib names by preflight.

Validation: scompile.py successfully compiled the complete final module on the server
in 1.8 seconds, exit code 0, without warnings. The initial membership elaboration error
was repaired by projecting the affine open to `U.1`. Every variable and universe is
explicitly bound. Both proofs are `by sorry`; nothing is proved at stage 2.

## Second reading by M1

I read the node statement, its dependency records, the Lean module, and Stacks
`equiv.tex`, Lemma `lemma-Ext-0-regular` (Tag 0FZ3), part (1), at the source
text around line 1645.

The node's objects and hypotheses match the Lean as follows. The regular scheme
`X` is `(X : Scheme.{u})`; regularity is the affine-neighbourhood predicate
`∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsRegularRing Γ(X, U)`. Quasi-compactness
is `[CompactSpace X]`, local Noetherianity is `[IsLocallyNoetherian X]`, and the
finite dimension is `(d : ℕ)` with `hdim : X.dim = (d : WithBot ℕ∞)`. The coherent
modules are `F G : X.Modules` with the two `RingedSpace.IsCoherent` hypotheses.
The Ext object is exactly `Ext F G i` from `def-sc-ext-sheaf`, with its required
`[HasExt.{u} X.Modules]` size binder. The conclusion is
`Subsingleton (Ext F G i)` for every `i` with `d < i`, which renders vanishing.
The P1 specialization introduces `(k : Type u) [Field k]`, uses exactly
`ProjectiveLine (Spec (CommRingCat.of k))`, takes coherent `F G` on that scheme,
and concludes `Subsingleton (Ext F G i)` for every `2 ≤ i`. No hypothesis or
conclusion clause is missing or strengthened.

The source states a regular Noetherian scheme of finite dimension and coherent
`F,G`, with Ext zero for `n>d`; the first Lean theorem has precisely those
conditions in the project's recorded encodings. The second is the `d=1`
projective-line specialization and correctly quantifies over arbitrary field
characteristic. The universe `u` is shared by the field, scheme, modules, and
Ext infrastructure. Edge cases checked: `d=0` only forces positive-degree
vanishing; `i=d` and `i=0` are not claimed; `i=2` is included in the P1 clause;
zero modules cause no issue; the empty scheme cannot satisfy the stated finite
natural dimension equality under `Scheme.dim`'s convention.

I searched Mathlib and the project with LeanSearch (service error), Loogle,
LeanFinder, and `rg`/grep for regular/coherent Ext statements and the exact
node/declaration names. Only abstract projective/injective dimension results
and unrelated local Ext results were found; no existing declaration states this
scheme theorem. The dependency declarations were opened, including `IsRegularRing`,
`Scheme.dim`, `RingedSpace.IsCoherent`, `Scheme.Modules.Ext`, and the recorded
projective-line carrier. No duplicate notion, hollow definition, unbound
variable, or private dependency copy was found.

No mismatch was found, so no source, node statement, or Lean signature was
changed. The module compiled cleanly with `scompile.py`; both theorem proofs
remain `sorry` as required for stage 2.
