## Worker report

The module `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedCoverCompatibleUnitRoots`
states `AlgebraicGeometry.Scheme.UniversalCover.pointedCover_compatible_unit_roots`.
Only that theorem is postponed, with `sorry`. The three coordinate helpers have real data:
`pointedCoverRing s = Γ(cover s, ⊤)`, `pointedCoverBase s` is pullback along `proj s`
composed with the canonical ΓSpec isomorphism, and `pointedCoverEval s` is pullback
along the existing marked point `pt s`, followed by the ΓSpec isomorphism for Ω.
Thus H is the coordinate ring of the actual affine pointed limit, not an arbitrary ring.

Hypothesis and clause correspondence:

- Positive prime p: `(p : ℕ) (hp : p.Prime)`; Mathlib primes are positive.
- Commutative characteristic-p E: `[CommRing E] [CharP E p]`.
- Nonempty connected affine spectrum: `[ConnectedSpace (Spec (.of E))]`;
  ConnectedSpace includes nonemptiness. No domain or reducedness assumption is imposed.
- Geometric point: `[Field Ω] [IsAlgClosed Ω]` and
  `s : Spec (.of Ω) ⟶ Spec (.of E)`, exactly the recorded inline interface.
- Pointed limit cover: `cover s`, `proj s`, `pt s` from the recorded cover module.
  Affineness of proj over affine Spec E identifies this with Spec of its global sections.
- N_p: the existing `AlgebraicGeometry.ProEtale.TameRootOrder p`, namely
  `{n : ℕ // 0 < n ∧ n.Coprime p}`. Its owning landed definition node is added
  to stmt_deps, without changing any mathematical hypothesis.
- Compatible primitive geometric labels: the first existential `ζ`, with
  `∀ n, IsPrimitiveRoot (ζ n) n.val` and its divisibility power equation.
  IsPrimitiveRoot says the power is one and n divides every exponent giving one,
  so it means multiplicative order exactly n, as required.
- Finite étale root schemes: the next conjunct asserts `IsFinite` and `Etale`
  for Spec of the canonical map E → AdjoinRoot (X^n-C(a)), for every unit a.
- For ANY prescribed label: `root a n c` is quantified over the subtype
  `c : {c : Ω // c ^ n.val = (Spec.homEquiv s).hom (a : E)}`.
  Hence the theorem applies to every compatible primitive family, not just the
  initial witness, by specializing a=1 and taking c=ζ n.
- Normalized sections: the `∃! f` is over ring homomorphisms
  `AdjoinRoot (X^n-C(a)) →+* pointedCoverRing s`. Its first clause fixes every
  coefficient from E; its second fixes the marked value of the universal root.
  These are exactly sections over Spec H with prescribed geometric-fibre label,
  by the affine spectrum correspondence and AdjoinRoot universal property.
- Values and uniqueness: `root ... ^ n.val = pointedCoverBase s a`,
  `pointedCoverEval s (root ...) = c.val`, `IsUnit (root ...)`, and
  `∀ b, b^n=... → pointedCoverEval s b=c.val → b=root ...`.
  The latter also forces evaluation of the unique section at X to equal root.
- Compatible powers: the next clause sends any compatible labels c,d at m,n
  to the equation `root a m c ^ (m.val / n.val) = root a n d`.
- Other power maps: the following clause compares `root a n c ^ k` with
  `root (a ^ k) n d` for labels satisfying `c.val ^ k = d.val`.
- Unit differences: specialize a=1 and any primitive c; distinct residues are
  `a % n.val ≠ b % n.val`, and the displayed difference is `IsUnit`.
- Every finite family of units: `(r : ℕ) (a : Fin r → Eˣ)` with witnesses
  `b : Fin r → TameRootOrder p → Ω`, their root equations and all divisibility
  equations. Any finite indexed family is reindexed by Fin r. Applying root to
  these labels gives the asserted compatible units in H, with exactly these equations.
- Pointed naturality: the last clause quantifies over another such E', Ω', s',
  ring maps f, ι and the induced map g between the actual cover coordinate rings.
  `g.comp (pointedCoverBase s) = (pointedCoverBase s').comp f` is the base square;
  `(pointedCoverEval s').comp g = ι.comp (pointedCoverEval s)` is the point square.
  The conclusion identifies g(root) with every root upstairs with transported label.
  In particular it identifies it with the normalized section for that label.
  This is an intrinsic characterization valid for all such pointed maps; it does not
  introduce a replacement cover or an arbitrary root construction. It includes changes
  of geometric field and commutes with both preceding power-map equations.

Dependency declarations read and used:

- `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; geometric points are inline.
  Read `Scheme.SpecToEquivOfField` in Mathlib.AlgebraicGeometry.ResidueField as well.
- `Sheaf.AlgebraicGeometry.FundamentalGroup.PointedLimitCech`: the entire
  `PointedLimitCechCoordinates` interface and `nonempty_pointedLimitCechCoordinates`;
  its imported `WeilConjectures.AlgebraicGeometry.FundamentalGroup.UniversalCoverConstruction`
  supplies `cover`, `proj`, `pt`, `toObj`, affineness, connectedness and splitting.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Sheaf.Paper.StrictLocalKummerTameModule`: `ProEtale.TameRootOrder` (reused).
- All stated proof dependency modules are imported: the upstream primitive-root
  existence and primitive-root trivialization modules; Mathlib.Data.ZMod.Units
  (`ZMod.unitsMap_surjective`); Mathlib.CategoryTheory.CofilteredSystem
  (`nonempty_sections_of_finite_inverse_system`, evaluation surjectivity);
  Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure; Mathlib.RingTheory.AdjoinRoot
  (`powerBasis'`, `liftAlgHom`, their generator/evaluation equations);
  upstream `RootSplitAwayCoverEtale` (`Scheme.root_split_away_cover_etale`).
  The finite-scheme spectrum and affine homomorphism correspondence are provided
  by the public cover imports. No proof dependency is replaced or omitted.

Sources: read the root algebra and invertible derivative argument in Stacks 03PL,
`literature/stacks-project/etale-cohomology.tex`, lemma-kummer-sequence. The node's
nine proof steps, including finite compatible selection, marked uniqueness,
idempotent-polynomial unit difference and pointed naturality, are reproduced in the
theorem docstring. The recorded cover's full signature and normalization fields
were read, together with the upstream construction of its limit and marked point.

Edge cases checked before finalization: n=1 forces the normalized root of unity to
one and its distinct-residue clause is vacuous. n=m makes power exponent one.
p=2 allows every positive odd order. Fin 0 handles the empty unit family.
The zero ring is excluded by ConnectedSpace of its empty spectrum (also by the
geometric point); nonreduced connected rings remain allowed. No invertibility
of a difference is inferred merely from different values at the marked point.
Identity base changes, arbitrary pointed pullbacks satisfying the two squares,
and proper geometric field extensions are all retained. All types/universes and
variables are explicit (`set_option autoImplicit false`); the geometric point and
cover use the existing compatible universe u convention. No statement correction,
new node, dependency replacement or disputed statement was necessary.

Searches (the initial three tool results are retained in sandbox searches.jsonl):

- msearch leanfinder: "Universal pointed finite etale cover carries compatible prime
  to characteristic roots of units and primitive roots of unity with invertible
  differences". Eight results, headed by StandardEtalePair and its HasMap interface;
  none states this normalized compatible universal-cover result. Rechecked after resume.
- msearch loogle: "IsPrimitiveRoot, AdjoinRoot.liftAlgHom". Zero combined results.
  Their separate declarations were read directly; neither supplies the target theorem.
- msearch grep: "compatible.*root|primitive.*root" in RingTheory/RootsOfUnity.
  Twenty-five hits for individual primitive roots and standard roots-of-unity lemmas,
  no pointed-cover theorem.
- rg in lean/WeilConjectures and lean/Sheaf for pointed root/compatible unit-root
  concepts: KummerSystem concerns powers of a fixed prime in fields, and existing
  tame modules define the order set and parameter towers, not this statement.
- rg for the exact item id in lean/WeilConjectures: no declaration.
- rg for each proposed helper name and the theorem name in both source roots:
  no collisions. DAG search for TameRootOrder found its existing owning node, reused.

Validation: prescribed scompile.py compiled the module in sandbox and library modes
cleanly (15.3 s / 16.1 s for the first complete signature); later dry-run compilation
checks the final imports and verbatim node signature again. No local build was run.

## Second reading by Q121

Self-audit of the node against the final module; no independent worker was started,
as the dispatch expressly forbids starting agents. The maintainer's independent review
remains the independent reading. On rereading, the partial draft only made a section
unique after its H-value was already fixed. I changed the unique-homomorphism predicate
to fix its geometric label and added uniqueness of the H-root by its equation and label.
I also made finite étaleness of the actual AdjoinRoot scheme explicit. The geometric
label normalization, divisibility powers, general powers, primitive unit differences,
finite-family labels and field-changing pointed naturality now each have an explicit
clause, as matched above. The existing TameRootOrder was reused and its node added to
stmt_deps after checking that this introduces no dependency cycle. All helper data are
actual global-section maps; no choice from a sorried existence theorem defines data.
