## Worker report

The module Sheaf.AlgebraicGeometry.TameInertiaSNCRootQuotient states
AlgebraicGeometry.exists_tame_inertia_snc_root_quotient, with one `sorry` and no new
definition. It is the node's underlying-scheme assertion, without a log conclusion.
The repair removes the added simultaneous-root API dependency: the signature now writes
`Algebra.pthRootAlgebra n r A t` and `Ideal.Quotient.mk _ (MvPolynomial.X i)` inline,
using the existing `def-sfb-parameter-root-algebra` declaration.

Source read: ILO IX Proposition 2.1 and proof, printed pp.133--134 (PDF pp.139--140),
including the displayed simultaneous-root invariant presentation; VI 2.2--2.3 is the
source for the diagonal action. The current blueprint ancestor
literature/blueprint/latest/blueprint/sec-deligne-laumon-a1/sk-p-dl-a1-perverse/
lem-per-artin-gabber-affine-curve.md was also read. The seven-step proof docstring
follows the node's proof, including the strict-local invariant-basis argument.

Hypotheses, clause by clause:

- `Y Z : Scheme.{u}`, `[IsNoetherian Y]`, `[IsNoetherian Z]`, and `hY : IsRegularScheme Y`
  give exactly the two Noetherian schemes and regularity of Y.
- `D : Y.IdealSheafData`, `hD : D.IsNormalCrossingsDivisor` use the recorded etale-local
  parameter-product definition, allowing non-strict global branches. `hred` says every
  affine boundary ideal is radical, the reduced closed-subscheme condition. The open U
  is written throughout as `D.support.compl`.
- `G : Type v`, `[Group G] [Finite G]`, and `a : G →* Aut Z` are the finite group and
  scheme action. Its universe is independent of the scheme universe.
- `q`, `[IsFinite q]`, `[Surjective q]` and `hinvariant` give the finite surjective
  invariant projection. `hsheaf` expresses the invariant structure sheaf on EVERY open:
  injectivity of q.app and image equal to the invariant sections, with pullbacks compared
  to restrictions on their common subopens. `horbits` gives transitivity on field-valued
  geometric fibres. Invariance supplies the reverse implication in orbit equality.
- `hnormal` requires each stalk of Z to be an integrally closed domain. It does not
  require Z itself to be integral, regular, or excellent.
- `hfree` gives a dense invariant open with trivial geometric stabilizers. `hetale`
  is Etale of q restricted over U. `htame` requires the cardinal of each geometric
  stabilizer to be a unit in its algebraically closed field. This is equivalent to
  invertibility in the underlying residue field because that field embeds in Ω.
  No unit condition on |G| is imposed.
- The selected `Ω`, field and algebraic closure instances, and `z` give the geometric
  point above `z ≫ q`. `H : Subgroup G` and `hH` identify H exactly with its stabilizer.
  H is a binder with its defining equality rather than a second stabilizer definition.

Conclusions, clause by clause:

- `A`, its CommRing and Noetherian instances, `e : Spec A ⟶ Y`, and `yT` give the pointed
  affine etale T, with `Etale e` and `yT ≫ e = z ≫ q`.
- `n r : ℕ`, `0 < n`, and `IsUnit (n : A)` render n≥1 and local invertibility, with
  r=0 permitted. `ζ : Aˣ`, its nth-power equation, and the unit conditions for all
  0<b<n render the primitive root condition exactly.
- The List.ofFn tuple localized at the selected prime is a sublist of a regular system
  of parameters `s`, using IsLocalRing.IsRegularSystemOfParameters. Its localization
  is the local ring of Spec A at that point, with its canonical A-algebra structure.
- `e ⁻¹ᵁ D.support.compl = PrimeSpectrum.basicOpen (∏ i, t i)` is exactly the asserted
  equality of the pulled-back U with D(t₁⋯tᵣ).
- `Algebra.pthRootAlgebra n r A t` is the existing actual polynomial quotient
  A[X_i]/(X_i^n-t_i). `Multiplicative (Fin r → ZMod n)` is the group (Z/n)^r written
  multiplicatively so that Mathlib's Subgroup and quotient-group constructions apply.
- `ρ` is an A-algebra action specified by its values on every root. Thus it fixes A
  and sends x_i to ζ^(g_i) x_i. Its equations determine the action uniquely by the
  polynomial quotient universal property; this is not an arbitrary unconstrained map.
  `S : Subalgebra A ...` has membership EXACTLY the K-invariance condition.
- W is written directly as `Spec S`. An arbitrary W with the required isomorphism can
  be replaced by this spectrum, and conversely this spectrum itself is the required W.
  `w`, `zW`, Etale w, the pointed equation, and the square with the coefficient spectrum
  map give the neighbourhood of Z and its map to T. No H-action on W is asserted.
- `c` is the coefficient map from A to R=O^sh_(Y,zq), pinned by its structural and
  geometric-point equations. `ρR` is the same diagonal action after applying c to
  parameters and ζ. `C` is EXACTLY its K-invariant subalgebra.
- `j` is pinned on coefficients and each root; it is the canonical root-algebra
  coefficient extension. `jS` is its restriction to invariants, pinned by equality
  after inclusion. `ι : C ≃+* strictHenselizationRing z` gives the strict-local
  invariant presentation. Its base-map equation uses the published canonical
  strictHenselizationMap q z; its equation through jS and w and its point equation
  ensure this comparison extends the SAME affine chart, not an unrelated isomorphism.
- `θ : Gamma/K ≃* H` gives the stated abstract group identification (inverse direction
  of H ≅ Gamma/K). `α h` is pinned to the actual pointed strict-local lift of a(h): its
  spectrum map lies over the original automorphism and preserves point evaluation.
  Uniqueness of the canonical pointed strict-local lift determines α, so no alternative
  action is substituted. The final equation says rotation by g on C equals the actual
  inertia action α(θ([g])) after ι. Hence it is the required equivariance, not merely an
  abstract group isomorphism. A ring automorphism is contravariant to its spectrum;
  the explicit equation fixes the convention.
- `r = 0 → Subsingleton H ∧ IsIso (strictHenselizationMap q z)` states the trivial
  inertia and identity strict-local cover up to its canonical structural isomorphism.

Dependency declarations read and used:

- Sheaf.AlgebraicGeometry.IsRegularScheme: AlgebraicGeometry.IsRegularScheme, defined as
  IsLocallyNoetherian ∧ the published stalkwise IsRegular.
- Mathlib.AlgebraicGeometry.Noetherian: IsLocallyNoetherian and IsNoetherian.
- Mathlib.RingTheory.IntegralClosure.IntegrallyClosed: IsIntegrallyClosed; IsDomain is
  the corresponding Mathlib domain class, used at each stalk, not a duplicate normality.
- Mathlib.AlgebraicGeometry.Morphisms.Etale: AlgebraicGeometry.Etale.
- Mathlib.AlgebraicGeometry.Morphisms.Finite: AlgebraicGeometry.IsFinite.
- Mathlib.FieldTheory.IsAlgClosed.Basic: IsAlgClosed; geometric points use the recorded
  inline field-valued convention (ResidueField.SpecToEquivOfField was read).
- WeilConjectures.RingTheory.IsRegularSystemOfParameters:
  IsLocalRing.IsRegularSystemOfParameters (span of list equals maximal ideal, length
  equals Krull dimension).
- WeilConjectures.AlgebraicGeometry.StrictHenselization: Scheme.strictHenselizationRing
  and Scheme.strictHenselizationScheme, the actual affine-pointed colimit and spectrum.
- Sheaf.AlgebraicGeometry.NormalCrossingsDivisor:
  Scheme.IdealSheafData.IsNormalCrossingsDivisor.
- WeilConjectures.RingTheory.PthRootAlgebraLocal: Algebra.pthRootAlgebra; reused through
  the direct `Algebra.pthRootAlgebra n r A t` declaration recorded by
  def-sfb-parameter-root-algebra. Its quotient body and parameter order were read.
  The images of polynomial variables are written as
  `Ideal.Quotient.mk _ (MvPolynomial.X i)`; no extra root definition is introduced.
- WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap:
  Scheme.strictHenselizationStructuralMap.
- Sheaf.Paper.StrictHenselizationPointEvaluation: Scheme.strictHenselizationPointEvaluation.
- Sheaf.AlgebraicGeometry.StrictHenselizationCanonicalMap: Scheme.strictHenselizationMap
  and strictHenselizationMap_existsUnique, which package the recorded
  Sheaf.Paper.StrictHenselizationFunctoriality interface canonically.

All recorded proof-dependency modules are plain imports. Unstated proof nodes are
left for stage 3; Mathlib proof leaves are supplied by Morphisms.Etale (composition),
RingTheory.Spectrum.Prime.Topology (lying over), RingTheory.Ideal.GoingUp (maximal above
maximal), and FieldTheory.Galois.Basic (finite fixed-field degree, Galois fixed field,
and normalAutEquivQuotient with its restriction formula). These are not extra postponed
helper theorems. The theorem docstring records all seven proof steps.

Edge cases checked: r=0 gives the empty product 1, trivial root group, and strict-local
identity; n=1 gives ζ=1 and vacuous intermediate-exponent conditions; trivial G is
allowed. Empty schemes satisfy all scheme predicates but have no selected geometric
point, so the pointed theorem has no instance there. In characteristic p, p may divide
|G| when geometric inertia is prime to p; the theorem adds no global invertibility.
Disconnected normal Z and non-strict globally self-intersecting D remain allowed.
The selected point excludes a zero coefficient ring automatically. Parameter lists use
Fin r and arbitrary local dimension, with no ambient dimension bound. All universes and
variables are explicitly bound, and no local notation, local instance, or helper copy
is introduced.

Searches for existing notions/statements:

- msearch.py leanfinder: "Tame inertia quotient normal crossings local parameter root
  cover invariant ring": 8 hits on unramified-at-prime and Dedekind ramification/inertia
  degrees, none the scheme normal form.
- msearch.py loogle: `"Abhyankar"`: 0 hits.
- msearch.py grep: `Abhyankar|tame.*ramif|ramif.*tame`, AlgebraicGeometry: 0 hits.
- msearch.py leansearch: "Normal crossings tame finite quotient has local invariant
  simultaneous root algebra presentation": 8 hits on finite presentations and standard
  etale presentations, none this theorem.
- rg in lean/WeilConjectures and lean/Sheaf for RootQuotient, InertiaSlice,
  NormalCrossings, group actions, and tame/root invariants found the reused definitions
  and the single-divisor RootPowerMapInvariants/StrictLocalRootInvariants results;
  those do not state this multi-parameter scheme theorem. The exact node-id search
  in WeilConjectures returned no declaration. DAG searches found the existing normal
  crossings divisor and root algebra nodes. The simultaneous-root API node was removed
  from `stmt_deps` during repair because only its plain abbreviations had been used; no
  new notion requires a new node.

Validation: scompile.py compiled this file both in its isolated sandbox and as its
library module, with exit 0, no errors, and no unexpected warnings. The first compile
caught an invalid attempt to use a closed support as a scheme; hred now uses the exact
affine radical-ideal condition instead. No STATEMENT-DISPUTED issue remains.

## Second reading by Q82

I reread the node and the complete Lean signature after the successful compile, in
this same worker session. No independent sub-agent was started, as the dispatcher
explicitly forbids it; the maintainer supplies the independent delivery review.

The second pass matched each hypothesis and conclusion as tabulated above. It checked
that the normality hypothesis is stalkwise and permits disconnected schemes; that
stabilizers fix geometric points, not just underlying points; that the order condition
uses those stabilizers, not G; and that both T and W are affine pointed etale
neighbourhoods. It checked that the parameter list is localized at the selected point,
that K acts through the specified diagonal root action, and that S and C are the full
invariant rings. It checked the strict-local coefficient, structural, point, and action
equations, which prevent replacing the actual action or the affine chart by arbitrary
data. The r=0 clause and n=1 case were read explicitly. No mathematical mismatch was
found; only the initial invalid support-to-scheme projection required repair before
the clean compile. No changes to the natural-language statement were made.


## Repair of returned delivery a0f43eb79054

H2 was the sole return point. The saved packet was first dry-run unchanged; it passed
mechanical preflight and compilation as 487f34819d0, but still contained the returned
ownership defect. The repair takes the maintainer's inline option. The public import
of Sheaf.RingTheory.ParameterRootAlgebra is replaced by
WeilConjectures.RingTheory.PthRootAlgebraLocal, whose Algebra.pthRootAlgebra is owned by
def-sfb-parameter-root-algebra. Every use of Algebra.ParameterRoot.Ring is expanded to
that existing declaration with the correct exponent, number of parameters, coefficient
ring and tuple. Every use of Algebra.ParameterRoot.root is replaced by
Ideal.Quotient.mk _ (MvPolynomial.X i). The theorem node
lem-sfb-simultaneous-root-algebra-api is dropped from the added stmt_deps.

The current shared main copy still has no Lean record for this item; its original
statement, proof and other fields are retained byte-for-byte as JSON values. This
repair changes only the saved delivery's Lean signature, import, lean record, added
stmt_deps and report. The delivery wrapper rebases the packet on current main.

The accepted strict-henselization-functoriality dependency remains: its canonical map
is determined by the published unique-existence theorem, rather than being an arbitrary
choice. All pointed, coefficient, action, invariants and r=0 equations were reread after
expanding the abbreviations. In particular the base-changed quotient has coefficient
ring Scheme.strictHenselizationRing (z ≫ q), and j maps the displayed quotient variable
to that same displayed variable. Both substitutions are definitional expansions, so
all mathematical clauses and edge cases in the original report remain valid.

Validation after repair: scompile.py compiled the sandbox and library module with
exit 0 (3.8 and 4.5 seconds), with no errors or unexpected warnings. No new declaration,
new node, postponed helper, statement correction or additional hypothesis was needed.
