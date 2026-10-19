## Worker report

The module states `AlgebraicGeometry.Etale.sepclosed_regular_proper_curve_trace` and
introduces only specialized wrappers for the canonical closed-point immersion and its
regular Gysin class. The sole theorem proof is `sorry`. No natural-language statement
or dependency record is changed, and there are no new nodes.

Source read: ILO, Exposé XVII, proof of Proposition the project server, printed pp.271–272
(PDF pages 277–278). The source characterizes the trace by sending the enlarged
closed-point Gysin class to the residue degree. The nine-step proof from the node is
included in full mathematical detail in the theorem docstring, including generic
multiplicity after inseparable extension, the positive Kummer sign, and uniqueness.

Hypothesis and conclusion correspondence:

- A separably closed field is `(k : Type u) [Field k] [IsSepClosed k]`.
- The k-scheme D is `(D : Scheme.{u}) (f : D ⟶ Spec (.of k))`.
  This explicit structure map also supplies the residue-degree map.
- Regularity is `hregular : IsRegularScheme D`, retaining both local Noetherianity
  and stalkwise regularity. Integrality is `[IsIntegral D]`, including nonemptiness.
- Properness is `[IsProper f]`; dimension one is `topologicalKrullDim D = 1`.
  Topological dimension is the scheme dimension; the ring Krull-dimension dependency
  explicitly identifies its ring notion with the dimension of the spectrum.
- The coefficient prime, exponent, and invertibility are `(ℓ : ℕ) (hℓ : ℓ.Prime)`,
  `(n : ℕ) (hn : 1 ≤ n)`, and `hℓk : IsUnit (ℓ : k)`.
- Λ is the recorded `regularClassCoefficients ℓ n = ULift (ZMod (ℓ ^ n))`, the
  harmless universe lift required by the dependency's coefficient-category convention.
- Ordinary H²(D,Λ(1)) is `Ext (regularClassTwist ℓ n D 0)
  (regularClassTwist ℓ n D 1) 2`: derived Hom from the constant rank-one module
  computes ordinary derived global sections, in the ordinary small-etale site.
- A canonical trace is the unique `≃ₗ[regularClassCoefficients ℓ n]` from this
  group to the coefficient ring. This includes bijectivity and coefficient linearity;
  uniqueness expresses exactly the characterization in the source and proof Step 9.
- Every closed point is quantified by `z : closedPoints D`. Its canonical inclusion
  is `D.fromSpecResidueField z.val`, not an arbitrary immersion or residue-field model.
  `sepclosedCurvePointImmersion` gets its closedness from the Mathlib equivalence
  `isClosed_singleton_iff_isClosedImmersion`, applied to `z.property`.
- The predicate positively asserts `∃ hreg : SepclosedCurvePointRegular D z` before
  evaluating the class, so regularity is not an extra assumption or a vacuous implication.
- `sepclosedCurvePointClass` selects the unique normalized Gysin family from
  `regular_immersion_class_calculus`, evaluates it in codimension one at twist zero,
  and composes with `Ext.mk₀ (supportedConstantUnit ... i)`. This is the recorded
  equivalent supported Ext presentation of Cl_i(1), with support enlarged to D.
- Its trace is `(f.residueDegree z.val : regularClassCoefficients ℓ n)`.
  `Scheme.Hom.residueDegree` is precisely the finite rank of κ(z) over κ(f(z));
  the canonical identification κ(f(z)) = k gives the required [κ(z):k].
- `hD : IsUnit ((ℓ ^ n : ℕ) : Γ(D, ⊤))` is universally quantified only as
  proof evidence to evaluate the dependency's family, exactly as in the existing
  degree-normalized trace interface. It introduces no new hypothesis: map
  `(hℓk.pow n)` along `((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom` and rewrite
  natural casts to obtain hD. Proof irrelevance removes dependence on that witness.

Dependency declarations read and reused:

- Mathlib.FieldTheory.IsSepClosed: `IsSepClosed`.
- Sheaf.AlgebraicGeometry.IsRegularScheme: `AlgebraicGeometry.IsRegularScheme`.
- Mathlib.AlgebraicGeometry.Properties: `AlgebraicGeometry.IsIntegral`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `AlgebraicGeometry.IsProper`.
- Mathlib.RingTheory.KrullDimension.Basic: `ringKrullDim`; the scheme condition uses
  Mathlib.Topology.KrullDimension's `topologicalKrullDim`.
- WeilConjectures.AlgebraicGeometry.DerivedCategories and its coefficient imports:
  the ordinary module-valued small-etale derived category, not a pro-etale category.
  The current server source was read with `scompile.py --source`.
- Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist: `Scheme.finiteEtaleTateTwist`.
  The recorded `regularClassTwist` specializes its signed extension at zero and one.
- Mathlib.AlgebraicGeometry.ResidueField: `Scheme.residueField`,
  `Scheme.Hom.residueFieldMap`, `Scheme.Hom.residueDegree`, `Scheme.fromSpecResidueField`.
- Sheaf.AlgebraicGeometry.RegularImmersionClassCalculus:
  `regularClassCoefficients`, `regularClassTwist`, `RegularImmersionClassFamily`,
  `RegularImmersionClassLaws`, `regular_immersion_class_calculus`.
- The public dependency closure supplies `supportedConstantUnit` from
  Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary and the canonical twists.
- Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear supplies the genuine module
  structure and linear interpretation of Ext; no custom cohomology action is introduced.

All recorded proof-dependency modules are imported (with Mathlib matches used for
Mathlib leaves). The not-yet-stated proof inputs normalization-field-extension,
weighted-components, birational-degree-invariance, and Jacobian-torsion-Pic have no
module to import; they are still named explicitly in the proof docstring.

Edge cases checked: the empty scheme is excluded by integrality itself, rather than
by a new hypothesis; n = 1 is included and n = 0 is excluded by the node. Characteristic
zero and positive characteristic different from ℓ are both retained. Separably closed
imperfect fields are allowed: smoothness and geometric reducedness of D are not assumed.
Purely inseparable closed-point degrees are not replaced by one. All multiplicities
in pullback divisors and the generic multiplicity of D_K are retained in the proof.
All universe variables and term variables are explicitly bound; coefficients are lifted
one level to match the existing Gysin family without restricting the scheme universe.

Searches for an existing statement:

- msearch LeanSearch, query “A regular integral proper curve over a separably closed
  field has a trace isomorphism on second etale cohomology with roots of unity, sending
  the cycle class of a closed point to its residue degree”: eight hits about algebraic
  field traces and stalks; none states this etale-cohomology theorem.
- msearch LeanFinder, query “trace isomorphism second etale cohomology regular proper
  curve separably closed field closed point degree”: eight unrelated algebraic and
  trace results; no match.
- msearch Loogle, `Ext, AddEquiv`: zero hits; no trace theorem found.
- msearch Mathlib grep, `trace|Trace` in AlgebraicGeometry: zero hits.
- rg of the node id and regular/etale trace patterns in WeilConjectures: no match.
- rg of lean/Sheaf found Curve.DegreeNormalizedTrace and TraceCupNaturality.
  DegreeNormalizedTrace requires an algebraically closed field and a smooth connected
  curve and normalizes point classes to one. It does not cover the present separably
  closed, possibly nonsmooth curve or its possibly nontrivial residue degrees.
- rg of all introduced full-name suffixes in Mathlib, WeilConjectures and lean/Sheaf:
  no existing declarations.

The Gysin dependency's docstring carries its own STATEMENT-DISPUTED warning about
uniqueness from its normalization laws. This delivery uses its exact recorded interface;
it does not assert a resolution of that separate stage-3 proof concern. No counterexample
or statement fault was found in the present trace node.

Validation is recorded below after the prescribed wrapper checks.

Compilation diagnostic: the main module compiled cleanly through scompile.py when the
unchanged current source Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback was explicitly
included in the same wrapper invocation. The wrapper compiled that source (13.8 s),
RegularImmersionClassCalculus (40.0 s), and the trace module (26.9 s), all below 60 s.
A direct probe then recognized both FiniteEtaleTwistPullbackData and its canonical
selection, which the current server source declares. However, repeated ordinary
invocations without explicitly resupplying this unchanged published dependency fail
inside RegularImmersionClassCalculus lines 69 and 80 with unknown constant
AlgebraicGeometry.Scheme.finiteEtaleTwistPullbackData, always returning the same
snapshot path and timing [49.1 s]. A direct import probe likewise recognizes only the
older theorem etaleFiniteTwistPullback, not the later structured declarations.
Adding the direct relevant import before the Gysin import does not repair the mismatch.
This is an overlay/source-versus-artifact mismatch, not an absent mathematical interface.
No launcher, shared source, artifact, or dependency record was edited to work around it.

Required dry run: `deliver2.py NS lem-per-sepclosed-regular-proper-curve-trace
--no-push` fails before preflight with the same stale-overlay unknown-constant error
at RegularImmersionClassCalculus lines 69 and 80. Nothing was pushed. The finished
statement, exact node lean record and correspondence report remain in this sandbox.
Ordinary single-file compilation was retried, the current server sources were read,
and explicit unchanged dependency compilation was tested successfully. Tool repair
is required so ordinary delivery compilation uses that current dependency source.

## Resumed packet validation (2026-10-18 UTC)

Retained the earlier packet. The required initial delivery dry run and a repeated
ordinary dry run both failed before preflight at RegularImmersionClassCalculus
lines 69 and 80: unknown constant
`AlgebraicGeometry.Scheme.finiteEtaleTwistPullbackData` (snapshot 4c80ab5310a9).
The prescribed `scompile.py --source
Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback` confirms that the current published
source defines this exact constant, its data structure and its existence theorem.
The shared current source agrees. No supported freshness option is exposed by
`deliver2.py` or `scompile.py`; neither tool was changed.

Revalidated with the prescribed scompile.py wrapper, explicitly supplying the
unchanged read-only EtaleFiniteTwistPullback source followed by the saved trace
module. This succeeded without warnings; the dependency compiled in 13.8 s,
RegularImmersionClassCalculus in 40.0 s, and the final library trace module in
17.2 s. This is diagnostic compilation only: no dependency copy or record was
added to the delivery. The recorded theorem signature matches the source exactly,
all source lines meet the 100-character limit, and the node differs from the current
shared node only in `lean`. There is no maintenance repair note for this item.

A final required deliver2.py --no-push after the successful explicit compilation
still failed with the same two unknown-constant errors, this time in snapshot
1492be376fef (53.4 s). Thus even a changed overlay snapshot selects an artifact
missing declarations present in the published source. This is a reproducible
compiler-overlay dependency-resolution tool failure, not a missing interface in
the mathematical statement. Nothing was pushed. The original module and node
record are retained unchanged for resumption after the overlay tool is repaired.


## Resumed packet validation (2026-10-18 UTC, successful retry)

Retained the saved module and node. The initial required dry run reproduced the
unknown `Scheme.finiteEtaleTwistPullbackData` errors in the published
RegularImmersionClassCalculus dependency. The prescribed `scompile.py --source`
confirmed that the published finite-Tate module declares this constant.
An explicit scompile.py invocation with that unchanged read-only dependency and
the saved trace module compiled both, including the Gysin consumer, without
errors or warnings. The trace library compilation took 17.4 seconds.

The subsequent ordinary deliver2.py --no-push invocation now succeeds:
`OK (dry run): commit 061f871294 passes the preflight and compiles; nothing pushed`.
The earlier tool-failure entries above are historical and no longer block delivery.
No shared source, launcher script, or artifact was edited.

Self-check: opened the saved module and its node and compared each hypothesis
and conclusion with the correspondence under Worker report. The statement still
uses the separably closed field, regular integral proper dimension-one curve,
prime-power coefficients invertible over the field, ordinary small-etale H²,
and canonical Gysin point classes with their residue-degree normalization.
The closed-point regularity witness is asserted in the conclusion, rather than
assumed. No mathematical change was needed. Compared with the current shared
node, only the lean field differs; the recorded theorem signature matches the
source verbatim and every Lean line is at most 100 characters. All variables
and universes are explicitly bound, and the only postponed proof is the named
theorem with its nine-step proof docstring. No repair note exists for this item.

## Second reading by NS

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
