## Worker report

The module `Sheaf.AlgebraicGeometry.HilbertTestComponentRetention` records the two
assertions of `lem-per-hilbert-test-component-retention`. Its three declarations, all in
`AlgebraicGeometry.HilbertSamuel`, are:

- `globalComponentDimensions`: the actual set of global topological component dimensions
  through the specified point, implemented with full data and no postponed proof.
- `hilbert_test_blowup_component_retention`: inclusion of profiles under strict transform,
  and equality conditional on equality of the extended Hilbert--Samuel functions.
- `hilbert_test_sequence_component_retention`: the shifted profile formula at every prefix
  of a supplied finite admissible test sequence, and the two bounds on a common open
  neighborhood of every retaining point.

The two theorems have `sorry` proofs. Their docstrings give the eight steps of the accepted
DAG proof, split as steps 1--4 and 5--8. No definition, instance or construction uses `sorry`.
The item's statement, statement dependencies, proof and proof dependencies are unchanged.
There are no new nodes or dependency repairs. The small profile helper names precisely the
formula introduced in this node, under the owning-module helper authorization in the brief;
it supplies no independent additional assertion or notion.

### Hypotheses and clauses: the single blowup

1. **Finite-type Q-scheme X in a smooth finite-type ambient, locally closed.** The schemes
   are `{X Z : Scheme.{u}}`; `p : Z ⟶ Spec (.of (ULift.{u} ℚ))` and `i : X ⟶ Z` are
   their specified structure maps, and `[IsImmersion i]` allows a genuinely locally closed
   embedding. `[Smooth p] [QuasiCompact p]` say the ambient is smooth of finite type
   (smooth implies locally of finite type). `[LocallyOfFiniteType (i ≫ p)]` together with
   `[QuasiCompact (i ≫ p)]` states the finite type of X. `ULift` changes only the carrier
   universe of Q, allowing arbitrary scheme universe `u`.
2. **No reducedness.** Neither theorem has an `IsReduced`, integral, equidimensional or
   generic-reducedness assumption. The strict transform is scheme-theoretic.
3. **The raw function, residue transcendence degree, summation and extended function.**
   These are the existing `HilbertSamuel.localFunction`, `summation`, and `function` from
   `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`, publicly available through the recorded
   presentation dependency. `localFunction` is the natural-number extraction of the length
   of the stalk modulo maximal-ideal power `n+1`. `function (i ≫ p) x` uses the actual
   residue-field algebra induced by the structure map and iterates summation
   `Cardinal.toNat (Algebra.trdeg (ULift ℚ) (X.residueField x))` times. Finite type makes
   both lengths and transcendence degrees finite, so these extractions lose no information.
   Nonclosed points are included.
4. **Underlying topological component dimensions.**
   `globalComponentDimensions X x` unfolds to
   `{d | ∃ W : Set X, W ∈ irreducibleComponents X ∧ x ∈ W ∧ topologicalKrullDim W = d}`.
   `W` has its subspace topology. Thus this is exactly `P_X(x)`, using sets of distinct
   dimensions, without multiplicities. `WithBot ℕ∞` retains the conventional empty and
   infinite dimensions; actual finite-type irreducible components have finite dimensions.
5. **A smooth closed center C inside X.** `C : Z.IdealSheafData` is the ambient center;
   its closed immersion is the canonical `C.subschemeι`. The morphism
   `c : C.subscheme ⟶ X` and `hc : c ≫ i = C.subschemeι` specify its scheme-theoretic
   inclusion into X, not just a point-set inclusion. Since i is an immersion, this is the
   closed subscheme of X induced by the ambient center. `[Smooth (C.subschemeι ≫ p)]`
   is smoothness over Q. These are exactly the actual center data needed to speak about
   its ambient blowup for a locally closed immersion.
6. **Local constancy of H_X on C.** `hconstant` is
   `IsLocallyConstant (fun a : C.subscheme ↦ function (i ≫ p) (c a))`.
   It restricts the function of X to C, rather than using the Hilbert--Samuel function of C.
7. **The scheme-theoretic strict transform in the ambient blowup.**
   `C.strictTransform i` is by definition `strictTransform i C.blowupMap C.support.compl`;
   this is the scheme-theoretic image of the unchanged open in the actual fiber product.
   Its morphism to X is `strictTransformToSource i C.blowupMap C.support.compl`.
   No arbitrary replacement map, topological closure, or chosen unrelated blowup is used.
8. **A point y over x in C.** `(x : X) (hx : x ∈ Set.range c)` gives precisely x in C,
   while `(y : C.strictTransform i)` and `hy` identify its image with x.
9. **Inclusion without equality.** The first conclusion is literally
   `globalComponentDimensions (C.strictTransform i) y ⊆ globalComponentDimensions X x`.
10. **Equality conditional on H equality.** The second conclusion is an implication from
    equality of `function` at y, using its composite structure map to Q, and at x, to
    equality of the two profiles. In particular no hypothesis requires all original
    components to survive; components contained in C are allowed to disappear.

### Hypotheses and clauses: finite presentation tests

1. **A supplied finite sequence and every prefix.** `n : ℕ` is its length;
   `history : Fin (n + 1) → Embedded (ULift.{u} ℚ)` supplies the n+1 embedded schemes,
   and `steps : ∀ j : Fin n, Step (history j.castSucc) (history j.succ)` supplies the
   successive geometric operations. `marks` supplies each marked ideal, not an existence
   assumption that might choose unrelated transforms. The conclusion quantifies over
   every `j : Fin (n+1)`, including zero and the last prefix, and every point y there.
2. **An actual initial presentation.** `hpresentation : Presents (marks 0)` uses exactly
   the recorded dependency. This includes its initially empty test boundary and agreement
   after every finite admissible test, with existence and quantification over transforms.
   Initial finite type is `hfinite : QuasiCompact (history 0).p`: `Embedded.smooth` and
   `Embedded.closed` supply local finite type and the closed embedding. Therefore both
   the ambient and its closed X are finite-type Q-schemes. Here the starting neighborhood
   is the supplied embedded presentation neighborhood of the node, not an arbitrary
   unrelated germ or a reduced replacement of it.
3. **Admissibility and genuine transforms.** `hadmissible` applies each existing
   `Step.Admissible` to the current marked-ideal cosupport; along a presentation that is
   the intrinsic retaining locus. `htransforms` is `Step.Transforms` for those same marks.
   In `Step.schemeTransform`, an admissible blowup has an isomorphism with the actual
   scheme-theoretic strict transform, while both auxiliary tests have the prescribed
   cartesian squares. `Step.geometry` uses the actual center blowup, line projection,
   zero section and two distinct labelled boundary components. `Step.levelTransform`
   changes the level by summation exactly at a line test. Nothing here replaces these
   constructions by arbitrary maps or assumes the profile retention being concluded.
4. **Earlier ordered centers stay separate from the test boundary.** The theorem is
   uniform in any externally retained ordered earlier-center ideals: they impose no
   restriction on `steps`, and are never inserted into `Embedded.boundary`.
   `Presents (marks 0)` starts this boundary empty; each `Step.geometry` updates it by
   ordered strict transforms plus the new exceptional ideal (or ordinary pullback plus
   the zero section for a line). Thus the allowed exceptional-intersection tests concern
   only this fresh test boundary. No additional hypothesis demands normal crossings with
   an unrelated earlier-center history. The numerical assertion requires no comparison
   of earlier-center lists and asserts none; the lists can be carried separately unchanged
   as external history data, exactly as in the presentation interface's `CommonComparison`.
5. **The line count r at a prefix.** `r : Fin(n+1) → ℕ`, `hrzero : r 0 = 0`, and
   `hrstep : r j.succ = r j.castSucc + if (steps j).kind = .line then 1 else 0` uniquely
   specify the actual number of preceding affine-line tests. This is a combinatorial
   encoding of the count, not a stronger numerical invariant or an extra assumption about H.
6. **Initial bound H_X ≤ H_0.** `hbound` uses the existing lexicographic `HilbertSamuel.le`
   to compare `function ((history 0).i ≫ (history 0).p) x` with `(history 0).level`.
   Pointwise order on numerical sequences is deliberately not used.
7. **Initial profile on the equality locus.** `hprofile` says that every x with its
   extended function equal to `(history 0).level` has `globalComponentDimensions ... x = P₀`.
   `P₀ : Set (WithBot ℕ∞)` is supplied; no nonemptiness is imposed on its equality locus.
8. **Retaining the extended level after r line products.** The premise in the conclusion
   is `function ((history j).i ≫ (history j).p) y = (summation^[r j]) (history 0).level`,
   exactly H_j(y) = Lambda^r H_0, independent of a closed-point convention.
9. **The entire shifted profile.** The first conclusion is equality with
   `(fun d : WithBot ℕ∞ ↦ d + (r j : WithBot ℕ∞)) '' P₀`, exactly `{d+r | d ∈ P₀}`.
10. **A local neighborhood with both bounds.** The second conclusion supplies an actual
    scheme open `U`, containing y, and for every z in U simultaneously the lexicographic
    bound by the same iterated initial level and profile containment in that same shifted
    P₀. The profiles remain those of the whole current scheme, not new profiles computed
    after replacing it by U. This implies the node's assertion locally along the retaining
    locus and does not assert a global bound on all points of every cartesian test.
11. **No existence or resolution assertion.** All schemes, tests, marks, admissibility,
    transforms, presentation, initial level and initial profile are inputs. Neither
    theorem constructs a presentation, normalized invariant or resolution tower.

### Dependency declarations read and used

- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` from
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType` and `AlgebraicGeometry.QuasiCompact`
  from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact` (the latter publicly imported
  by the former). Finite type is their conjunction; there is no invented bundled property.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion` from
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; the locally closed variant is
  `AlgebraicGeometry.IsImmersion` from `Mathlib.AlgebraicGeometry.Morphisms.Immersion`.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth` from
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, also the property stored by `Embedded`.
- `def-weil-pbc-module-length`: `Module.length` from `Mathlib.RingTheory.Length`.
- `def-kun-transcendence-degree`: `Algebra.trdeg` from
  `Mathlib.RingTheory.AlgebraicIndependent.Basic`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and the induced
  residue-field algebra map from `Mathlib.AlgebraicGeometry.ResidueField` (used inside
  the existing `function`; its exact definition was read).
- `def-weil-irreducible-components`: `irreducibleComponents` from
  `Mathlib.Topology.Irreducible`.
- `def-kun-topological-krull-dimension`: `topologicalKrullDim` from
  `Mathlib.Topology.KrullDimension`, applied to the actual component subspace.
- `def-nagata-global-blowup`: `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and
  `blowupMap` from `WeilConjectures.Blowup.Gluing`.
- `def-nagata-strict-transform`: `AlgebraicGeometry.strictTransform`,
  `strictTransformToSource`, and `Scheme.IdealSheafData.strictTransform` from
  `WeilConjectures.Compactification.StrictTransform`.
- `def-trf-hilbert-samuel-presentation`: `Embedded`, `Marked`, `Marked.cosupport`, `Step`,
  `Step.Admissible`, `Step.Transforms`, `Presents` and their fields from
  `Sheaf.AlgebraicGeometry.HilbertSamuelPresentation`. The full module, including
  `PresentsThrough`, cartesian/strict transform clauses, and separate earlier history
  in `CommonComparison`, was read. The existing numerical definitions used transitively
  are `localFunction`, `summation`, `function` and `le` from `HilbertSamuelInvariant`.

Every already stated proof dependency's module is imported privately (or already publicly
for its role in the signature). Mathlib proof leaves are imported from Noetherian,
AssociatedPrime.Localization, Spectrum.Prime.Topology, ReesAlgebra, and
AlgebraicIndependent.TranscendenceBasis. Project proof imports cover domain dimension,
associated graded rings, the flat graded-fiber lift, strict-transform closed comparison,
affine blowups, relative Proj base change, jet-diagram control, regular-sequence blowup
charts, and regular-sequence graded polynomials. Four proof nodes have no Lean record in
the read base and are not needed to state the result: `lem-per-scheme-near-point-normal-cone`,
`lem-trf-graded-polynomial-vertex-regularity`, `lem-per-retained-test-boundary-regularity`,
and `lem-per-scheme-hilbert-samuel-test-presentations`. They are named explicitly in the
proof docstrings where appropriate. No dependency notion needed by the signature is missing.

### Edge cases checked before writing

- Empty schemes, empty centers and empty retaining loci: the quantified points or
  equality premises are absent; no unjustified `Nonempty` requirement was added.
- A whole component contained in C, or all components contained in C: the strict transform
  may lose that component or be empty. The first conclusion is inclusion; equality is
  conditional on an actual near point and extended-function equality.
- Nilpotents: no reduction is taken and no reducedness assumption is imposed. The strict
  transform remains the scheme-theoretic image; the proof's minimal-prime associatedness
  argument works for nonreduced Noetherian rings.
- Nonclosed points and arbitrary residue extensions: the existing function includes the
  residue transcendence degree, not only the closed-point raw function.
- Non-equidimensional and disconnected X: dimensions form a set of all component
  dimensions through the point. Distinct same-dimensional components count only once.
- n=0: there is one prefix and no step; `hrzero` makes its shift zero, so the conclusion
  recovers the initial profile and its local containment neighborhood.
- No line tests: the recurrence forces every r to zero; a line test increases r by exactly
  one. No arbitrary natural-number shift is allowed.
- Empty initial equality locus and arbitrary supplied P₀: the theorem has retaining-point
  premises and adds no existence assertion. `Presents` also prevents freely inventing
  nonmatching transformed cosupports.
- Auxiliary intersection tests use two distinct labels and cartesian pullback, with the
  evolving fresh boundary fixed by `Step`; they are not silently changed to strict
  transforms or restricted to centers smooth inside X.
- Universe `u` is explicit throughout. The base Q is lifted into that same universe, so
  arbitrary scheme sizes are allowed without constraining a test universe separately.

No statement correction or STATEMENT-DISPUTED issue was found. The local bound is explicitly
local; the future proof does not need the stronger global cartesian-test bound flagged in
the stage-1 review of the boundary regularity input.

### Searches and source check

All Mathlib searches used the prescribed `msearch.py Q66 lem-per-hilbert-test-component-retention`:

- `leanfinder`, query `Hilbert Samuel near points preserve irreducible component dimension
  profiles under blowups and finite presentation tests`: eight hits concerning prime-spectrum
  chains and local support-dimension inequalities, including
  `Module.supportDim_le_supportDim_quotSMulTop_succ` and
  `ringKrullDim_le_ringKrullDim_add_spanFinrank`; none states either retention assertion.
- `loogle`, query `AlgebraicGeometry.strictTransform, topologicalKrullDim, irreducibleComponents`:
  zero hits; unknown identifier `AlgebraicGeometry.strictTransform` (a project declaration).
- `grep`, query `HilbertSamuel|componentProfile|dimensionProfile`, subdirectory
  `AlgebraicGeometry`: no Mathlib hits.
- `leansearch`, query `Hilbert Samuel equality under blowup retains the dimensions of every
  irreducible component and every finite admissible presentation test`: eight hits about
  algebra-presentation dimensions, base-change stability and ring-equivalence dimension,
  not Hilbert--Samuel near points or finite test retention.

Local `rg -n` searches in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
`dimensionProfile|componentDimension|componentProfile|ComponentProfile`, and later the
chosen declaration names found no existing exact statement or named global profile.
The broader definition search found only `localComponentDimensions` in
`HilbertSamuelSmoothDimensionProfile`; its minimal-prime stalk quotient dimensions are
local-ring dimensions, not this node's global dimensions (a curve's generic point already
distinguishes the two). `HilbertSamuelEqualityComponentRigidity` was read: it only gives
the reduced equality clause, with neither the nonreduced inclusion nor finite-test clause.
It cannot be rebound as an exact statement of this node. The new names were also searched
in `dag/lean_names_upstream.json`, with no match. The profile helper is a real formula using
the existing component and dimension definitions, not another dimension convention.

Read BMT arXiv:0905.3580v1 at https://arxiv.org/html/0905.3580v1, especially sections 5.2,
6.1--6.3 and Remark 6.2: the three test kinds, initially empty test boundary, extended
function at arbitrary points, line summation and Gabber's component-dimension correction
agree with the existing interface and this statement. The proof-specific nonreduced
normal-cone and boundary arguments are exactly the separately named inputs in the node.

### Validation

`scompile.py Q66 lem-per-hilbert-test-component-retention` compiled the delivered module
against the live published server build with no errors or warnings (sandbox 2.2 seconds,
library-name compile 1.9 seconds). Both proofs remain `sorry`, as required for stage 2.
The node JSON uses indent 1, UTF-8 characters and a final newline; its `lean.statement`
is extracted verbatim from the first theorem signature before `:=`.

## Second reading by Q66

Author's second pass, not an independent reviewer: the dispatcher brief forbids starting
other agents, and the maintainer provides the independent delivery review.

Reopened the node statement and the complete module and matched the two paragraphs to the
two theorem signatures. In the first theorem the center factors scheme-theoretically
through the locally closed X, its smoothness is over Q, local constancy restricts H_X,
and y maps to the specified x in C. The conclusions are inclusion plus equality only under
extended H equality. There is no hidden reducedness or component-survival assumption.
In the second theorem the data contain every finite step and every marked transform;
Presents starts the fresh boundary empty, earlier-center history is not inserted there,
and the recurrence counts exactly line steps. The initial lexicographic bound and equality
profile are both hypotheses. Each prefix, including zero, has exactly the iterated extended
level in the equality premise, the full translated global profile in the conclusion,
and an open neighborhood satisfying both requested bounds. The open is in X_j, whereas
its profiles still use global component dimensions of X_j. No existence theorem is stated.
The helper unfolds to the node's own formula and does not use the different stalk-local
profile. Checked all binders and the explicit universe and lifted rational base. No mismatch
requiring a node correction was found; no dependency or auxiliary new-node module is needed.
