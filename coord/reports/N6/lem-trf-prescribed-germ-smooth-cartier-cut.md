## Worker report

This delivery states `AlgebraicGeometry.exists_prescribed_germ_smooth_cartier_cut` in
`Sheaf.AlgebraicGeometry.Morphisms.PrescribedGermSmoothCartierCut`, with `sorry` as its
entire proof. Four helper declarations construct the actual principal quotient spectrum,
its quotient immersion, a fibre pullback map, and the stalk map with equal image points
transported by `stalkCongr`. Their data contain no postponed proofs. These are canonical
constructions serving this node, not substitute hypotheses or independent notions.

The inherited BLOCKED concerned stage-1 delivery of the already split Q130 node. The
current node has reviewed stage-1 data, no Lean record, no repair note, and a stage-2
queue entry. Thus the stage handoff in brief-stage2 §0 applies. This delivery retains the
accepted statement and proof verbatim. The only changes are `lean` and addition of two
new existing-definition nodes to `stmt_deps`, as permitted in §5.

Hypotheses and clauses, in node order:

- Schemes and the smooth morphism: `{X S : Scheme.{u}} (f : X ⟶ S) [Smooth f]`.
  The point is `(x : X)` and its image is literally `f x`.
- The scheme fibre is `f.fiber (f x)` and its point is `f.asFiber x`. The ring R is
  `(f.fiber (f x)).presheaf.stalk (f.asFiber x)`, never an unrelated ring or model.
- The specified germ is `h : X.presheaf.stalk x`; `hh` places it in the maximal ideal.
  Its image is `(f.fiberStalkMap x).hom h`. `hregular` states injectivity of multiplication
  by exactly this element on R.
- `hdiff` gives a representative `b` of h on a neighbourhood V, with equality of its germ
  to h, and `f.relativeDifferentialValue V x hxV b`. This existing predicate is precisely
  nonvanishing of `d b ⊗ 1` in the stalk of the recorded sheaf of relative differentials
  tensored with κ(x). Every stalk element has a representative, and the universal
  derivation commutes with restriction, so this existential is exactly the specified
  germ's differential condition. It introduces no choice of a different germ, no
  nonzero arbitrary vector, and no extra regularity or freeness assumption.
- `(W : X.Opens) (hxW : x ∈ W)` covers every prescribed neighbourhood.
- Existential U, `hU : IsAffineOpen U`, `hxU : x ∈ U`, and `U ≤ W` give the affine
  neighbourhood contained in W. H is the actual section ring `Γ(X,U)` and
  `hU.fromSpec : Spec Γ(X,U) ⟶ X` is its canonical open immersion.
- `a : Γ(X,U)` and `X.presheaf.germ U x hxU a = h` preserve the specified germ exactly.
- `prescribedGermCut a` is literally `Spec (Γ(X,U) ⧸ Ideal.span {a})`, and
  `prescribedGermCutι a` is literally Spec of the quotient homomorphism into Spec H.
  `IsEffectiveCartierCenter` is asserted for this immersion, using the general scheme
  definition; it is not the curve-specific predicate.
- `Smooth (prescribedGermCutι a ≫ hU.fromSpec ≫ f)` says D is smooth over S.
- `∃! xD, (prescribedGermCutι a ≫ hU.fromSpec) xD = x` says both that it contains x
  and that the point above x is unique.
- `prescribedGermFiberMap (hU.fromSpec ≫ f) (prescribedGermCutι a) (f x)` is the actual
  pullback morphism D_s → U_s, not a new arbitrary immersion. Its effective Cartier
  property is separately required, so ambient Cartierness is not confused with its
  generally false preservation by arbitrary base change.
- The point y in the actual D_s is required to map to `f.asFiber x` under the actual
  fibre map D_s → X_s. Its projection to D is therefore the unique xD already specified.
- `e` is a ring equivalence from `R ⧸ Ideal.span {hbar}` to the actual stalk at y of D_s.
  For EVERY `c : R`, `e (Ideal.Quotient.mk _ c)` equals the actual fibre morphism's
  stalk map (transported along `hy`). This is a characterization of the canonical map,
  rather than a bare existence of an abstract isomorphism. In particular for any affine
  fibre chart and any fraction c/u (u avoiding the prime), the stalk map sends the germ
  of c to c mod a_s and the inverse germ of u to its inverse mod a_s. The quantified
  equality applies to this fraction and gives exactly the node's displayed formula.
  Conversely that chart formula determines the equality for every R element, since
  every stalk element is a fraction on an affine neighbourhood. Thus the characterization
  includes the formula on every chart, including its independence of the chosen chart.
- The final equivalence r identifies the target residue field with `X.residueField x`.
  For every original germ b, the displayed residue equation says that passage through
  the fibre quotient, e, and r gives exactly `X.residue x b`. Since the original residue
  homomorphism is surjective, this specifies the identity on the common κ(x), and fixes
  the identification r uniquely; it is not a mere abstract residue-field isomorphism.
- There are no Noetherian, closed-point, finite residue-extension, or separability binders.
  The single scheme universe u is arbitrary.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth` (the recorded definition).
- `Mathlib.AlgebraicGeometry.Fiber`: `Scheme.Hom.fiber`, `fiberι`, `asFiber`,
  `fiberι_asFiber`; fibres are the specified pullbacks along `fromSpecResidueField`.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor` and `stalkObj`; ring germs/stalks themselves
  are Mathlib's `TopCat.Presheaf.germ`/`stalk`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`, `residue`, and
  `Scheme.Hom.residueFieldMap` (the final equation uses the residue homomorphisms).
- `WeilConjectures.AlgebraicGeometry.Modules.Differentials`:
  `Scheme.Hom.relativeDifferentials`, `relativeDifferentialsDerivation`, and the
  recorded affine/restriction construction, used by the existing differential predicate.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`, `.Basic`, `.Map`: `TensorProduct`, `tmul`,
  `lift`, `ext'`, `LinearMap.rTensor`, used by the differential predicate's tensor value.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`; the affine open is
  rendered by `IsAffineOpen` and its `fromSpec` construction in `.AffineScheme`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  the actual quotient spectrum and quotient homomorphism implement this notion.
- `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier`:
  `IsEffectiveCartierCenter`, without dimension or curve hypotheses.
- New existing-definition node `def-trf-fibre-stalk-map` (the accompanying theorem
  `lem-sbc-scheme-fibre-stalk-quotient` remains in `proof_deps`):
  `Sheaf.AlgebraicGeometry.FibreStalkQuotient`, `Scheme.Hom.fiberStalkMap` and
  `fiberStalkMap_surjective_ker_quotientEquiv`.
- New existing-definition node `def-trf-relative-differential-value` (the accompanying
  theorem `lem-zl-hypersurface-nonzero-relative-differential` remains in `proof_deps`):
  `Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential`,
  `Scheme.Hom.relativeDifferentialValue` and
  `smooth_zeroLocus_of_relativeDifferentialValue`.

The already recorded proof modules are plain imports. The theorem docstring carries
all six proof steps, including affine realization, fibre regularity, the differential
criterion, preservation of Cartierness on the fibre through flatness of the quotient,
the localization formula, and the identity on the residue field.

Sources read: `literature/stacks-project/more-morphisms.tex`, the complete statement and
proof of `lemma-slice-smooth-given-element` (Tag 057C). Its stated pointwise smoothness
is used here in the globally smooth case required by this node. The extra explicit
fibre regularity and quotient assertions are the accepted node's specified refinement,
proved by its six-step plan. No statement correction or dispute is needed.

Edge cases checked: the empty scheme cannot supply x; the zero local ring cannot occur
at a point; relative dimension zero cannot meet the nonzero differential hypothesis.
On A¹_S the coordinate germ cuts out the zero section. At the nonclosed point (t) of
Spec k[t,u], the common residue field is k(u), retained by the canonical stalk/residue
equalities. In characteristic p the equation t^p has zero differential and is excluded,
while t remains allowed. Arbitrary non-Noetherian bases remain admitted. No closedness,
separability, or choice of a finite extension enters any binder. W may be X or any
smaller open through x; U cannot be empty because hxU is supplied.

Searches through the prescribed msearch.py wrapper:

- LeanFinder: “A prescribed germ on a smooth scheme with nonzero residue differential
  extends to a smooth effective Cartier divisor with canonical fibre local ring quotient”.
  Eight hits (smooth charts, spreading by germ-injectivity, smooth locus, function field),
  none with this assertion.
- Loogle: `AlgebraicGeometry.Smooth, AlgebraicGeometry.IsClosedImmersion`: zero hits.
- Mathlib grep: `prescribed|Cartier|hypersurface`, subdirectory AlgebraicGeometry: two
  unrelated elliptic-curve prescribed-j-invariant hits, no match.
- LeanSearch: “A smooth Cartier hypersurface extending a specified germ with nonzero
  differential”: eight hits on smoothness/formal smoothness and manifold differentials,
  no match.
- rg of the node id in `lean/WeilConjectures`: no hits. rg of prescribed germ/Cartier
  and smooth Cartier in `lean/WeilConjectures`, `lean/Sheaf/AlgebraicGeometry`, and
  `lean/Sheaf/TraceFormula`: related curve or hypersurface theorems only. In particular
  `exists_affine_flat_hypersurface_of_fiber_regular` only concludes flatness and finite
  presentation, and `exists_affine_smooth_effectiveCartier_hypersurface_slice` assumes a
  closed point with finite separable residue field and does not preserve a specified germ
  or state this quotient. Neither is an existing match.

Validation: the initial module compiled in sandbox and library modes via scompile.py
on the server (5.4 and 5.8 seconds). Final compilation and delivery checks are recorded
below after the final explicit dependency-import pass.

## Second reading by N6

This is a separate self-review pass; the dispatcher explicitly prohibits starting
another agent, and the maintainer supplies the independent review. I reopened the node
and final module and checked each binder and conjunction against the correspondence
above. I specifically checked that the nonzero differential belongs to the SAME germ h,
that the section a has germ exactly h rather than an associate, that the divisor is the
literal spectrum of H/(a), and that the fibre Cartier assertion concerns D_s → U_s.
I checked the target point y maps to the original fibre point, so uniqueness identifies
its projection with xD. The quotient equivalence is fixed on every element by the actual
fibre stalk map, and its residue-field identification is fixed on all original germs.
These equations retain the chart-independent fraction formula and the identity on κ(x).
There is no use of an arbitrary ring, arbitrary map, or unspecified tensor structure.
All helper definitions are explicit constructions. All universes and variables are
bound, and the only postponed proof is the named theorem attached to this node.
No mismatch or statement change was found. The second reading added explicit imports
of the recorded statement and proof dependency modules and added the two existing helper
definition nodes to stmt_deps. The review return below repairs the ownership records;
no dependency modules or changes to the Lean are needed.

Final validation: scompile.py compiled the final module cleanly in sandbox mode
(10.6 seconds) and library mode (6.2 seconds), with no errors or warnings.
`deliver2.py N6 lem-trf-prescribed-germ-smooth-cartier-cut --no-push` printed
`OK (dry run): commit 23c49282a57 passes the preflight and compiles; nothing pushed`.

## New nodes

`def-trf-fibre-stalk-map` owns the existing definition
`AlgebraicGeometry.Scheme.Hom.fiberStalkMap` in
`Sheaf.AlgebraicGeometry.FibreStalkQuotient`. Its self-contained statement defines the
canonical map from the source stalk to the pointed fibre stalk, with transport along
`fiberι_asFiber`, exactly as the existing composite does. Source: Stacks 0HA1,
`schemes.tex`, `lemma-local-ring-fibre`. LeanSearch and LeanFinder returned general
stalk and residue maps; Mathlib grep found `fiberι_asFiber`, not this composite.
The searches of DAG records and the two Lean trees locate the existing helper in the
published Sheaf theorem module, but no definition node owns it. Hence `existing: true`
records that declaration without a new module. Its only statement dependencies are
the scheme and scheme-fibre definitions; it uses no quotient theorem. Empty schemes
supply no point, and identity morphisms and nonclosed points need no extra assumptions.

`def-trf-relative-differential-value` owns the existing definition
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialValue` in
`Sheaf.AlgebraicGeometry.HypersurfaceNonzeroRelativeDifferential`. For an arbitrary
scheme morphism, open U, point z in U, and section a, it says exactly that the germ of
the universal relative differential of a, tensored with 1 in the residue field, is
nonzero. The residue homomorphism supplies the field's stalk-module structure.
Source: Stacks 057C assumption (2) and 01UM. LeanSearch and LeanFinder returned
residue evaluation, algebraic differentials and smooth loci; Mathlib grep had no hit.
DAG and source-tree searches found only the existing helper in the Sheaf theorem
module, without a definition node. The definition is therefore recorded `existing: true`.
Its statement dependencies are the scheme, relative differentials, module stalk,
residue field and module tensor definitions, with no smooth-hypersurface theorem.
The predicate is false for a zero differential (in particular a pth power in
characteristic p), and imposes no smoothness, closedness or finite residue extension.
The exact search-wrapper result records are retained in each node's `mathlib_searches`.

## Repair of independent return H.2

The return at immutable head `012e58b75862` found that the two theorem nodes had been
added to `stmt_deps` solely for the plain helper definitions. Replaced those additions
with `def-trf-fibre-stalk-map` and `def-trf-relative-differential-value`. Both theorem
nodes remain in `proof_deps` unchanged. The item statement, proof plan, full Lean source,
and Lean signature are unchanged. Comparison with current main before repair showed
only the retained `lean` record and the two former `stmt_deps` additions differed;
there was no accepted source change to incorporate. The initial saved-packet dry run
passed at `ef536b09efe`, before this required ownership repair.

Second reading of the repair by N6: reopened both helper definitions with their
source docstrings. `fiberStalkMap` is the transported `fiberι.stalkMap`, constructed
before the quotient theorem and independent of it. `relativeDifferentialValue` uses
the relative derivation, its module germ, and `TensorProduct.tmul` with the residue
module action, before the smooth-hypersurface theorem and independent of it. Compared
every binder and expression with the new definition nodes and their verbatim recorded
signatures. The new statement dependencies are exactly their explicit bracketed
citations. Both records use the already published declaration and add no duplicate
Lean file. The only return point is repaired; no mathematical statement correction
or additional theorem assumption is introduced.

Repair validation: scompile.py compiled the unchanged theorem in sandbox mode
(10.6 seconds) and library mode (6.2 seconds), cleanly. The repaired-packet dry run
identified two metadata requirements: the signature extractor starts at `def`, omitting
its preceding `noncomputable` modifier, and the live new-node schema requires
`import_flags`. The two existing-definition signatures now start at `def`, and both
nodes carry `import_flags: []`. No Lean source was changed for these metadata repairs.
