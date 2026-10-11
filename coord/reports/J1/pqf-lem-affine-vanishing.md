## Worker report

The module `Sheaf.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing` states
`AlgebraicGeometry.subsingleton_openModuleCohomology_of_isAffineOpen`; its only proof is
`sorry`. No definitions, dependency replacements, or statement corrections are introduced.

Clause-by-clause correspondence:
- “Let X be a scheme”: `(X : Scheme.{u})`, with the universe explicitly bound.
- “F an O_X-module”: `(F : X.Modules)`, the shared sheaves-of-modules carrier, definitionally
  `SheafOfModules (moduleRings X.toRingedSpace)`.
- “quasi-coherent”: `[F.IsQuasicoherent]`, Mathlib's predicate used by pqf-def-coherent.
- “any affine open U subset X”: `(U : X.Opens) (hU : IsAffineOpen U)`; Mathlib defines this
  as affineness of the induced open subscheme, without requiring X itself affine.
- “for all p > 0”: `(p : ℕ) (hp : 0 < p)`.
- “H^p(U,F)=0”: `Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F)`.
  This is a bundled additive group, whose subsingleton carrier means the group is zero.
  The functor is R^p of sections over U on O_X-modules, not an unconstrained cohomology object.

Dependencies read and used:
- pqf-def-coherent: `Sheaf.AlgebraicGeometry.Coherent`,
  `AlgebraicGeometry.RingedSpace.IsCoherent`. The module's docstring explicitly delegates the
  quasi-coherent clause to Mathlib `CategoryTheory.SheafOfModules.IsQuasicoherent` (locally a
  cokernel of maps between free modules). That predicate, not the unrelated coherent clause,
  is used here; on schemes it has the source's affine-local tilde interpretation.
- pqf-def-cohomology: `Sheaf.Paper.PQFCohomology`,
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, establishes the cohomological
  delta-functor on the shared `RingedSpace.moduleCohomology` and the higher direct image
  comparison. Its cohomology definition is R^p of module global sections.
- Added existing landed statement dependency def-sc-open-module-cohomology:
  `Sheaf.Topology.OpenModuleCohomology`,
  `AlgebraicGeometry.RingedSpace.openModuleCohomology`. Its full signature and docstring
  were read: it is the right derived functor of sections over U on the same module category.
  This addition cites the already established open-cohomology notation needed in the node;
  it creates no new node and changes no mathematical statement.
- Mathlib `AlgebraicGeometry.IsAffineOpen`, in `Mathlib.AlgebraicGeometry.AffineScheme`.

Source checked: https://stacks.math.columbia.edu/tag/01XB, Lemma 30.2.2, whose statement
has exactly these hypotheses and conclusion. The local literature checkout is absent, so
this primary source was opened on the web. The theorem docstring includes each of the
three node proof steps. It explicitly records the module/abelian-sheaf cohomology comparison
needed to apply the older lem-pc-affine-vanishing input; this is a stage-3 proof obligation,
not an extra hypothesis or a redefinition.

Edge cases checked before writing: the empty scheme and U = bottom remain admitted;
F = 0 remains admitted; p = 0 is deliberately excluded and p = 1 included. Arbitrary
non-Noetherian, non-separated schemes and every characteristic remain admitted. No
nonemptiness, finiteness, field, or ambient affineness assumption is present. The module
carrier and scheme share an explicitly bound arbitrary universe u, as in the established
cohomology API.

Searches for an existing statement:
- msearch.py leanfinder, query “higher cohomology of a quasi-coherent module on any affine
  open vanishes”: 8 hits, including Sheaf.H, cohomologyPresheaf, affine transition section
  lemmas, and an injective derived-category lemma; none is this module-cohomology theorem.
- msearch.py loogle, query `IsAffineOpen, SheafOfModules.IsQuasicoherent`: 0 hits, unknown
  identifier IsAffineOpen in the service index.
- msearch.py leansearch, query “higher cohomology quasi coherent module affine open vanishes”:
  service unavailable (Internal Server Error); no mathematical verdict inferred.
- msearch.py grep, query `affine.*cohomology|subsingleton_H_succ|openModuleCohomology`
  in Mathlib AlgebraicGeometry: 0 hits.
- rg in WeilConjectures and lean/Sheaf for affine vanishing, subsingleton_H_succ_of_isAffine,
  and openModuleCohomology found the older affine-scheme theorem and the shared open
  cohomology definition, but no requested affine-open module-cohomology statement.
- rg for the proposed declaration name across Mathlib, WeilConjectures, lean/Sheaf and
  dag/lean_names_upstream.json found no collision.
- rg for the item id in WeilConjectures found no attached declaration.

The upstream theorem was followed through the re-export Affine.lean to
WeilConjectures/AlgebraicGeometry/Cohomology/Affine/Cech.lean:247 and its full signature
and docstring read. It requires `[IsAffine X]` and concludes `Subsingleton (F.H (q+1))`,
using abelian-sheaf Ext cohomology. It is not an existing statement of the requested theorem
for arbitrary affine opens with the current shared module-cohomology definition.

Validation: server single-file compilation and deliver2.py --no-push dry run; the second
reading is intentionally left to the independent second reader.

## Second reading by J1

The node's objects, hypotheses, and conclusion were matched against the Lean signature:

- Scheme (X): Lean `(X : Scheme.{u})`; the universe is explicit and unrestricted.
- Quasi coherent module \mathcal F: Lean `(F : X.Modules) [F.IsQuasicoherent]`, the
  project/Mathlib quasi coherence predicate on the scheme's module category.
- Affine open (U \subset X): Lean `(U : X.Opens) (hU : IsAffineOpen U)`; this is
  affineness of the induced open subscheme and does not assume (X) affine.
- Positive degree: Lean `(p : ℕ) (hp : 0 < p)`; this excludes (p=0) and includes (p=1).
- Vanishing (H^p(U,\mathcal F)=0): Lean
  `Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj F)`;
  `openModuleCohomology` is the declared right derived functor of sections over (U) on
  the same module category, and `Subsingleton` expresses the zero additive group.

The Stacks source (Tag 01XB, Lemma 30.2.2) states precisely these hypotheses and clause.
No hypothesis is stronger than the source: there is no Noetherian, separated, finite type,
characteristic, nonempty, or ambient-affine assumption. The arbitrary universe `u` covers
empty schemes and opens, and the statement also covers the zero module and every
characteristic. The affine-open hypothesis is used semantically in the admitted proof even
though it does not occur in the conclusion term.

I read the dependency declarations. `F.IsQuasicoherent` is the recorded module predicate,
and `RingedSpace.openModuleCohomology` is the existing open-cohomology definition; neither
is a private replacement. The existing affine-scheme theorem
`subsingleton_H_succ_of_isAffine` is only the special case with an affine ambient scheme and
does not duplicate this affine-open statement. Searches recorded by the worker (LeanFinder,
Loogle, LeanSearch, grep, and repository searches) found no existing declaration of this
statement. No mismatch was found, so no source, node, dependency, or Lean changes were needed.

The module compiles with `scompile.py` and contains only the permitted `sorry` proof.
