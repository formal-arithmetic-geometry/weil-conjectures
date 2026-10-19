## Worker report

This is an existing-interface delivery. No new module, definition, theorem, or proof
is written. The existing module
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line` explicitly implements
`sk-d-lines` (its module docstring names that node), including its gluing and
Frobenius clauses. The primary record is its definition
`AlgebraicGeometry.ProjectiveLine.infinityChart`; `lean.declarations` records the
other constituents needed to cover the whole node, not merely a general
projective-space declaration. The declaration's signature is copied verbatim
from `def` through its return type, before `:=`; `S` is bound by the preceding
`variable (S) in`, and `u` by the module's `universe u`.

Source read: the complete current blueprint
`literature/blueprint/main-20261015/blueprint/sec-trace-formula/sk-d-lines/_section.md`.
There is no `coord/repair-notes/sk-d-lines.json` in the shared checkout.

Homogeneous-coordinate naming convention: write the source's `T_0` for the
upstream indeterminate indexed by `1`, and the source's `T_1` for the one indexed
by `0`. These are the two indeterminates of the same polynomial-ring construction;
the node specifies their names, not a separate externally fixed ordered basis.
Under this renaming upstream `[t:1]` is source `[1:t]`, and upstream `[1:z]` is
source `[z:1]`. In particular source infinity is `[0:1]`, exactly the upstream
point `[1:0]` after the same naming translation. No chart or infinity is changed.
The coordinate renaming applies to the integral model as well as both charts.
It is essential: identifying source `T_i` with upstream index `i` without this
translation would give the wrong ordered-chart reading.

Clause-by-clause correspondence:

- Finite field `F` from the coefficient setup: use `F := D.k₀` for
  `D : WeilConjectures.FiniteFieldDatum.{u}` underlying the setup. Its registered
  `field_base` and `finite_base` instances give `[Field D.k₀] [Finite D.k₀]`;
  `card_base` identifies `Nat.card D.k₀` with `D.q = D.p ^ D.a`. The geometry
  uses only this finite-field part; coefficients, derived-category choices,
  and the algebraic closure do not enter the definition of either line.
  In particular the finite field is not mistakenly replaced by `D.k`.
- Projective line with two homogeneous coordinates:
  `AlgebraicGeometry.ProjectiveLine (Spec (.of F))` abbreviates
  `ProjectiveSpace (ULift.{u} (Fin 2)) (Spec (.of F))`.
- Base change of the integral Proj model: `ProjectiveSpace` is literally
  `pullback (terminal.from S)
    (terminal.from (Proj.projectiveSpaceOverAffine n (ULift.{u} ℤ)))`.
  `Proj.projectiveSpaceOverAffine` is the Proj of the total-degree grading of
  `MvPolynomial n A`. Thus `n = ULift (Fin 2)` gives exactly the two-variable
  integral model; the terminal base is `Spec ℤ` with the usual universe lift.
- Affine line `Spec F[t]`: the chart domains are
  `𝔸(PUnit.{u + 1}; Spec (.of F))`. `AffineSpace.SpecIso` identifies this with
  `Spec (.of (MvPolynomial PUnit.{u + 1} F))`.
  Mathlib's `MvPolynomial.uniqueAlgEquiv F PUnit.{u + 1}` identifies this
  one-variable polynomial ring with `Polynomial F`, sending its single variable
  to `Polynomial.X` and preserving coefficients. This is the usual canonical
  polynomial presentation, not a different affine variety. The same object is
  used with coordinate name `z` for the second chart.
- First chart coordinate `t=T_1/T_0`: `ProjectiveLine.affineChart`, with
  `affineChart_eq_homOfSections`, is `[t:1]` in upstream coordinates.
  Its defining `standardOpenIso` is the chart where upstream coordinate `1`
  is nonzero and the remaining coordinate is its ratio to coordinate `1`.
  The preceding naming translation gives exactly source `t=T_1/T_0`.
- Second chart coordinate `z=T_0/T_1`: `ProjectiveLine.infinityChart`, with
  `infinityChart_eq_homOfSections`, is upstream `[1:z]`, hence source `[z:1]`.
- Gluing along `F[t,t⁻¹]=F[z,z⁻¹]`, with `z=t⁻¹`:
  `isPullback_affineChart_infinityChart` identifies the intersection with
  the basic open of the single coordinate on the affine line. Its transition
  morphism is `AffineSpace.homOfVector ... (fun _ => ... basicOpenUnit ... ⁻¹)`.
  Hence on this locus the second coordinate is the inverse of the first.
  The basic open of `t` in `Spec F[t]` is precisely `Spec F[t,t⁻¹]`.
  `opensRange_affineChart_sup_opensRange_infinityChart` says that these two
  open immersions cover the projective line. Together the cartesian overlap
  and cover are exactly the stated gluing description, not just two unrelated
  maps into the line.
- Complement of the first chart is the point infinity, defined by `z=0`:
  `ProjectiveLine.infinity` is literally
  `AffineSpace.zeroSection PUnit S ≫ infinityChart S`.
  `compl_opensRange_affineChart_eq_singleton F` says that the complement is
  the singleton consisting of its value at `IsLocalRing.closedPoint F`.
- Frobenius on the two charts:
  `affineChart_comp_eq_of_isFrobenius` and
  `infinityChart_comp_eq_of_isFrobenius`, for `[Field F] [Finite F]`, say that
  composing either polynomial chart inclusion with the `Nat.card F`-power
  Frobenius equals precomposing with
  `Spec.map (CommRingCat.ofHom (MvPolynomial.expand (Nat.card F)).toRingHom)`.
  `expand` fixes coefficients and sends the single variable to its `|F|`-th
  power, exactly `t ↦ t^|F|` and `z ↦ z^|F|`. Their hypothesis
  `Φ.IsFrobenius (Nat.card F)` identifies the morphism being described;
  it is not an additional restriction on a field or the chosen lines.
  Read the full `Scheme.Hom.IsFrobenius` definition and docstring in
  `WeilConjectures.AlgebraicGeometry.Frobenius`: over this finite field the
  characteristic/cardinality assumptions are the ones under which the
  predicate characterizes the actual power Frobenius, so there is no
  characteristic-zero/vacuous-predicate issue.

Dependency declarations read in full:

- `sk-d-setup` records `WeilConjectures.TraceFormulaCoefficientSetup` in
  `Sheaf.Paper.TraceFormulaCoefficientSetup`. Read its full signature,
  definition, and docstrings. It is parameterized by
  `F : FiniteFieldDatum`, a prime `l ≠ F.p`, a finite extension `E/Padic l`,
  and positive level `n`. Its chosen compactifications and preservation
  requirements do not participate in defining the lines. Read the underlying
  `WeilConjectures.FiniteFieldDatum` structure and its instance registration in
  `Sheaf.Paper.FiniteFieldFiber` to identify the finite field correctly.
  Since this delivery only records existing declarations, there is no module
  in which an import or a specialization of the setup needs to be repeated.

Locations of reused declarations:

- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` defines `ProjectiveSpace`,
  `Proj.projectiveSpaceOverAffine`, and the `ProjectiveLine` abbreviation.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Charts` defines
  `ProjectiveSpace.standardOpenIso` and `ProjectiveLine.affineChart`.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line` defines
  `ProjectiveLine.infinityChart`, `infinity`, both chart-coordinate equations,
  the overlap pullback, the cover, singleton-complement theorem, and both
  Frobenius chart equations listed in the record. Its public imports expose
  the preceding projective-space declarations and Mathlib's `AffineSpace.SpecIso`.
- `Mathlib.AlgebraicGeometry.AffineSpace` defines `AffineSpace.SpecIso`.
- `Mathlib.Algebra.MvPolynomial.Equiv` defines `MvPolynomial.uniqueAlgEquiv`;
  its full signature and data were read. The deprecated alias `pUnitAlgEquiv`
  is not used in the binding.

Edge cases checked before recording: characteristic two and the smallest field
are included; there is no assumption that `2` is invertible. `Nat.card F` is
positive and a power of the characteristic since `F` is a finite field, and
there is no arbitrary exponent or characteristic-zero specialization. The
point `t=0` belongs to the first chart but not the overlap; infinity belongs
to the second chart at `z=0` and is absent from the first. The overlap uses a
unit only on the basic open of `t`, so no inverse of zero is introduced.
The coefficient level `n=1` does not alter the geometric constructions.
`ULift (Fin 2)` and `PUnit.{u+1}` retain the universe of `F : Type u` and do
not restrict to universe zero. Empty/zero-ring bases are outside the finite-field
hypothesis, although the generic chart constructions themselves also cover them.

Searches (2026-10-17):

- `msearch.py ... leanfinder "Projective line over a finite field with standard
  affine charts, point at infinity and Frobenius coordinate power maps"`:
  eight hits on projectivization and elliptic-curve projective points, no exact
  scheme-interface match.
- `msearch.py ... loogle "AlgebraicGeometry.ProjectiveLine,
  AlgebraicGeometry.AffineSpace"`: zero hits with unknown identifier
  `AlgebraicGeometry.ProjectiveLine`; inconclusive for upstream declarations.
- `msearch.py ... grep "ProjectiveLine|projectiveLine|frobenius"
  AlgebraicGeometry`: zero hits from that search service; upstream text search,
  not this result, establishes the actual match.
- `msearch.py ... leansearch "Affine projective line scheme glued two affine
  charts inverse coordinate Frobenius"`: eight hits, including
  `AffineSpace.isoOfIsAffine_inv_appTop_coord` and field Frobenius facts;
  no combined line/gluing interface.
- `rg -n "sk-d-lines" /home/ubuntu/weil-src-slopmaster2/WeilConjectures`:
  exact hit in `AlgebraicGeometry/ProjectiveSpace/Line.lean:46`. Read that file
  in full, its imported chart definitions, and the base-change model.
- Project-wide `rg` for projective/affine lines in upstream and `lean/Sheaf`
  finds many consumers and separate cohomology/Proj-comparison nodes, but
  the above upstream module already gives this node's geometric interface.
  `rg` in Mathlib's `Algebra/MvPolynomial` finds `uniqueAlgEquiv`, completing
  the canonical one-variable polynomial interpretation.

No statement correction, missing dependency, new node, or disputed mathematical
statement. The source and upstream differ only in names of the two homogeneous
indeterminates, explicitly translated above. Only the node's `lean` field changes.

Validation: the required `deliver2.py Q82 sk-d-lines --no-push` checks all recorded
existing declarations with a compiler probe importing the recorded module,
then runs the maintainer preflight. The dry-run result is recorded below after
execution. No second reading is claimed by this worker, and nothing is pushed.

Dry-run outcome: `OK (dry run): commit 104ecbdba8 compiles and passes the preflight
except for the second reading, which the second reader writes; nothing pushed.`
All recorded names passed the existing-declaration compiler probe. The independent
second-reading section is intentionally left for the next worker, as the tool requires.

## Second reading by Q82

I read the node statement and the complete source section
`blueprint/sec-trace-formula/sk-d-lines/_section.md` (node sk-d-lines, order 2718),
then matched each clause with the recorded existing interface in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line`:

- The finite field is the `k₀` field in `FiniteFieldDatum` supplied by
  `WeilConjectures.TraceFormulaCoefficientSetup` (the `sk-d-setup` dependency);
  its registered `Field` and `Finite` instances are exactly the finite-field
  hypotheses used by the chart and Frobenius declarations.
- `AlgebraicGeometry.ProjectiveLine (Spec (.of F))` is
  `ProjectiveSpace (ULift (Fin 2)) (Spec (.of F))`. The latter is defined as the
  pullback of `Proj.projectiveSpaceOverAffine (ULift (Fin 2)) (ULift ℤ)`, hence is
  precisely the base change of `Proj ℤ[T₀,T₁]` over `Spec ℤ`. `AffineSpace.SpecIso`
  together with `MvPolynomial.uniqueAlgEquiv` gives each chart as `Spec F[t]` or
  `Spec F[z]`.
- `ProjectiveLine.affineChart` and `infinityChart` supply the two open immersions;
  `isPullback_affineChart_infinityChart` gives their cartesian overlap with the
  inverse-coordinate map, and
  `opensRange_affineChart_sup_opensRange_infinityChart` gives the covering/gluing
  clause. `infinity` and
  `compl_opensRange_affineChart_eq_singleton` give the complement point and its
  equation `z = 0`.
- `affineChart_comp_eq_of_isFrobenius` and
  `infinityChart_comp_eq_of_isFrobenius`, using
  `MvPolynomial.expand_natCard`, give the two maps `t ↦ t^{|F|}` and
  `z ↦ z^{|F|}` under `Scheme.Hom.IsFrobenius (Nat.card F)`.

The upstream index `0` is named `T₁` and index `1` is named `T₀` in the source
notation. Thus its `affineChart` `[a:1]` is the source chart `[1:t]` after this
coordinate-name relabelling, while its `infinityChart` `[1:z]` is the source
`[z:1]`; this is only a renaming of the two homogeneous variables and preserves
the stated ratios, overlap, and marked infinity. No extra Noetherian, finite-type,
characteristic, or coefficient hypothesis is introduced, and the setup's level
`n ≥ 1` does not alter these geometric objects. The declaration is generic in
the common universe `u`, so instantiating it at `Spec F` covers the node's case.

Edge cases checked: finite fields of characteristic two and the prime field are
included; `Nat.card F` is positive and equals the setup's `q`; `t = 0` lies only
in the first chart, `z = 0` is the marked infinity in the second, and inversion is
used only on the basic-open overlap. The generic projective-space construction
also has its empty-index behavior, while the node fixes two coordinates; no zero
ring or empty finite field satisfies the field hypothesis. No index, scheme, or
coefficient universe is silently restricted.

Searches were repeated with `msearch.py` (LeanFinder, Loogle, and LeanSearch
queries for projective-line charts, gluing, and Frobenius), `rg` over Mathlib,
`WeilConjectures/`, and the repository's `lean/Sheaf`; the exact upstream module
and declaration set above is the only matching scheme interface. `FiniteFieldDatum`
and `TraceFormulaCoefficientSetup` were read in full, as were `ProjectiveSpace`,
`ProjectiveSpace.Charts`, and `Frobenius`; no repair note exists for this item.

There is no statement correction, new definition node, dependency repair, hollow
definition, or disputed clause. The sandbox node changes only its existing `lean`
record; no Lean source file is needed. The existing-declaration probe and the
required dry run both compile cleanly and report `OK`.
