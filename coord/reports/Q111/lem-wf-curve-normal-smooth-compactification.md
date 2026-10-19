## Worker report

The module `lean/Sheaf/AlgebraicGeometry/Curve/NormalSmoothCompactification.lean`
states `AlgebraicGeometry.exists_smooth_projective_compactification_of_normal_curve`.
The field `k₀` is a finite field (`[Field k₀] [Finite k₀]`), `U₀` is a scheme in
universe `u`, and `p₀ : U₀ ⟶ Spec (.of k₀)` carries the separated, locally finite type,
and quasi-compact hypotheses.  These three classes render “separated scheme of finite
type over `k₀`”.  `[GeometricallyConnected p₀]` renders geometrical connectedness.
The explicit `hnormal` binder says at every point that the stalk is a domain and
integrally closed, exactly the normality convention used by the node.  The binder
`hdim : topologicalKrullDim U₀ = 1` renders pure dimension one.

The conclusion is `Smooth p₀`, followed by a witness `C₀`, its structure morphism
`q₀`, and an open immersion `j₀ : U₀ ⟶ C₀` (the instance binder
`(_ : IsOpenImmersion j₀)` makes the open immersion available to the complement
construction).  `IsSmoothProjectiveCurve q₀` supplies the smooth projective curve
properties, and `GeometricallyConnected q₀` supplies geometric connectedness.
`DenseRange j₀.base` is the dense open condition, and `j₀ ≫ q₀ = p₀` says that the
compactification is over `k₀`.  Finally `j₀.closedComplement` is Mathlib's canonical
closed subscheme cut out by the vanishing (radical) ideal of the complement, hence is
the reduced complement `D₀`; `IsFinite (j₀.closedComplement ≫ q₀)` says this reduced
boundary is finite over `k₀`.

The declaration imports `WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective`
for `IsSmoothProjectiveCurve` and the project normalization/closed-complement API
from `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`.  The proof is
left as `sorry` exactly as required at stage 2.  Its intended proof follows the node's
three proof paragraphs: normal dimension-one local rings give regularity and smoothness;
projective closure plus normalization gives the smooth projective compactification; and
the dimension-zero boundary argument gives finiteness and geometric connectedness.

Edge cases checked: `hdim = 1` excludes the empty and zero-dimensional schemes; no
nonemptiness hypothesis beyond what the stated dimension and geometric connectedness
already imply was added.  The finite-field hypothesis is used as `[Finite k₀]`, while
all schemes and morphisms share universe `u`; no smaller independent test universe is
introduced.  The empty boundary is allowed (its finite morphism conclusion is still
valid), and the reduced complement is canonical through the radical vanishing ideal.

Searches for an existing exact declaration:

- `msearch.py ... leanfinder` for “normal geometrically connected finite type curve over a
  finite field has a smooth projective compactification”: only generic normalization and
  projective-curve results; no exact match.
- `msearch.py ... loogle` for `IsProjective IsFinite normalization smooth projective
  compactification`: no compactification theorem (and `IsProjective` is not a Mathlib
  scheme-morphism identifier).
- `msearch.py ... grep` for `normal.*compactification|projective.*normalization`: no
  matching declaration.
- `rg` in `WeilConjectures`: found
  `AlgebraicGeometry.exists_smooth_projectiveCompactification` in
  `AlgebraicGeometry/Curve/Compactification.lean`, but its statement is different: it
  assumes Mathlib `IsCurve p`, `[GeometricallyConnected p]`, a stalk normality predicate
  and a dimension equality, and concludes a `Compactification` with `IsCurve c.g` and
  an explicit projective-space immersion.  It does not state this node's explicit
  separated/finite-type binders, arbitrary `C₀,q₀,j₀` witness form, or reduced-boundary
  finiteness clause, so it is not an exact existing match.
- `rg` in Mathlib for `normal`, `compactification`, and `closedComplement`: Mathlib has
  the generic normalization and `Scheme.Hom.closedComplement` definitions but no exact
  theorem for this node.

No `STATEMENT-DISPUTED` issue was found.

## Second reading by Q111

I reread the node JSON and the completed module independently.  The finite-field,
separated, finite-type, quasi-compact, geometrically connected, normal-stalk, and
pure-dimension-one hypotheses each have a corresponding Lean binder.  The first
conclusion is exactly `Smooth p₀`.  The existential witness contains a scheme, its
structure morphism, an open immersion with its required instance, smooth-projective
and geometrically connected curve structures, dense range, compatibility over the
base, and finiteness of the canonical reduced complement.  No hypothesis or conclusion
was added, dropped, weakened, or specialized; the closed-complement API is the radical
vanishing-ideal construction matching the node's reduced complement.


## Independent maintainer review, 2026-10-18

Reviewed immutable delivery 207245d56269bcc5acab69dc8a688b00a176ed75 using packet.md,
the snapshot node and all four statement-dependency nodes, their exact source declarations,
the master blueprint statement, its main-20261015 proof, and Stacks algebra.tex
lemma-separable-smooth (00TV) and morphisms.tex lemma-finite-projective (0B3I).

Clause checks:
- `[Field k₀] [Finite k₀]` permits every finite field, with no characteristic restriction.
- `p₀` is the structure map; `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact`
  express separated finite type exactly, using the scheme-conventions dependency.
- `GeometricallyConnected p₀` is Mathlib's geometrically connected morphism predicate:
  all field-valued base changes are connected, not merely the original scheme.
- `hnormal` requires integrally closed domain stalks. Finite type over a field makes the
  scheme locally Noetherian. In this setting normality and connectedness imply
  integrality; therefore `topologicalKrullDim U₀ = 1` and pure dimension one agree.
  The worker's claim that a dimension equality expresses purity needs this argument.
- `Smooth p₀` is the first conclusion. The witnesses C₀, q₀, j₀ and the open-immersion
  instance supply exactly a compactification over the base, through `j₀ ≫ q₀ = p₀`.
- `IsSmoothProjectiveCurve q₀` extends `IsIntegralCurve`, `Smooth`, and `IsProjective`.
  Its variety parent supplies integrality, separatedness and finite type; its curve
  parent supplies dimension exactly one. `GeometricallyConnected q₀` supplies the
  additional geometric connectedness clause.
- `DenseRange j₀.base` is density. `j₀.closedComplement` is the actual vanishing-ideal
  subscheme of the complement of the open range, not an arbitrary closed immersion.
  The upstream reducedness instance and range lemma verify it is the canonical reduced
  induced structure. `IsFinite (j₀.closedComplement ≫ q₀)` is finiteness of D₀ over k₀.

Edge cases: empty and dimension-zero inputs are excluded by the original hypotheses;
normal connected finite-type inputs cannot have mixed-dimensional components. Empty
boundary is permitted, as for a curve already projective. All finite characteristics
are covered. Universe u is explicitly bound and shared by the field and schemes as
required by the scheme morphism API; geometric connectedness uses Mathlib's standard
same-universe field tests, and no independent smaller test universe is imposed.

Independent searches: rg for `compactification.*normal`, `normal.*compactification`
and `projective.*completion` in upstream, side Sheaf and Mathlib found the upstream
`exists_smooth_projectiveCompactification`. Its conclusion gives a compactification,
an explicit projective embedding and finite underlying boundary, but does not state
finiteness of the reduced boundary morphism. Its hypotheses use the weaker IsCurve
bundle and a perfect field; it is useful prior work, not an exact replacement for this
whole statement. LeanSearch query “An integral smooth completion of a normal curve
with finite reduced closed boundary” returned generic normalization and Weierstrass
results; Loogle name query `"compactification"` returned zero hits. No duplicate notion
is introduced here; the new file contains one theorem and no definitions.

Findings repaired in the replacement module:
- H8: the original declaration docstring only listed tools. It did not carry the node's
  three proof steps, and its wording incorrectly suggested that the whole theorem was
  the statement of Tags 00TV and 0B3I. The replacement names the blueprint source and
  explains integrality/regularity/smoothness, closure/normalization/projectivity,
  finite reduced boundary, and connectedness after every field extension.
- H9 (brief-stage2 section 3): add ordinary imports of the recorded, stated proof
  dependencies: FiniteOverProjective, Curve.Compactification, Regular, Normalization,
  and Topology.KrullDimension. The two existing public statement imports are retained.
- The delivered report contains both required real sections but records no item-specific
  compiler result. Fresh compiler evidence is recorded below.

The theorem signature is unchanged byte for byte, including its trailing whitespace
before `:=`, and equals the node's lean.statement. No statement_change or citer audit
is required. No helper construction, dependency repair, or new DAG prerequisite is
needed. No hollow data, extra local proof, local notation, or silent universe restriction
was found. All theorem proof content remains `sorry`. No pro-etale substitute or
infinity/dg/model machinery is used. The item and its dependency IDs have no intersection
with origin/newtargets-dag:coord/route-pivot-dropped.txt, and there is no item-specific
route-pivot repair note. Only the lean field was added to the node in this delivery.


### Fresh per-file compilation evidence

Both per-file reproductions used the prescribed wrapper, with no global build:

1. `python3 /home/ubuntu/weil-launcher-nt/scompile.py Q111
   lem-wf-curve-normal-smooth-compactification
   snapshot/lean/Sheaf/AlgebraicGeometry/Curve/NormalSmoothCompactification.lean`
   returned exit code 0, no Lean errors or warnings. Wrapper output: sandbox 7.7 s;
   library 59.6 s; private artifacts under `/dev/shm/nt-tmp/nt-local-compile-tmgn4egm/.lbuild`.
2. The same command with
   `fixes/lean/Sheaf/AlgebraicGeometry/Curve/NormalSmoothCompactification.lean`
   returned exit code 0, no Lean errors or warnings. Wrapper output: sandbox 3.3 s;
   library pipeline 239.9 s; private artifacts under
   `/dev/shm/nt-tmp/nt-local-compile-lnn41qnz/.lbuild`.

The installed scompile.py currently implements a server-side persistent side-source
overlay (`nt_srv_compile.py --wire-confirm`), despite the brief's earlier local-overlay
wording. I used that prescribed wrapper unchanged. It snapshots side dependencies,
keeps individual Lean invocations at the default 60-second limit, and confirms failures
through nt_compile.py. The reported library pipeline time includes dependency/overlay
work and is not an increased individual-file timeout. Transport multiplexing messages
were printed but both calls completed normally. No item-specific old compile transcript
was supplied in the immutable report; these are fresh reproductions, not an attribution
of a recorded worker run.

Final finding: no substantive defect; land using the two complete replacement files.
The immutable delivery itself needs H8/H9 repairs, hence FIX rather than PASS.
