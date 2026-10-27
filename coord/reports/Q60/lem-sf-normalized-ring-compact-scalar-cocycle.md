## Worker report

Item: lem-sf-normalized-ring-compact-scalar-cocycle. The new module is
`Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle`, with main declaration
`WeilConjectures.NormalizedRingCompactScalar.normalizedRingCompactScalarCocycle`.
It states the node using an explicit proposition-valued `Laws` record. Its only theorem
has proof `sorry`; every input record and predicate has actual data. The node statement and proof are unchanged. The H2 repair below adds three definition
owners to stmt_deps, including one new existing:true definition node; it introduces
no new Lean construction. Support/Scalar/Associator/Unit merely bundle the inputs stipulated in
this assertion; Normalized and Laws spell out its hypotheses and conclusions.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* The prime ell is `l : ℕ` with `[Fact l.Prime]`. The global finite-field datum is
  `D : FiniteFieldDatum.{u}` and the characteristic inequality is `hl : l ≠ D.p`.
  `D.k` is the chosen algebraic closure of its finite base field.
* `X Y : Scheme.{u}` carry `Over (Spec (.of D.k))` and the two pairs of
  `LocallyOfFiniteType`/`QuasiCompact` instances on their structure morphisms. This
  expresses finite type over k. `f.IsOver` expresses the k-morphism condition;
  `IsSeparated f`, `LocallyOfFiniteType f`, `QuasiCompact f` express separated finite
  type. Neither scheme's structure morphism has an IsSeparated hypothesis.
* `c : Compactification f` supplies exactly the open immersion `c.i`, proper map `c.g`,
  intermediate scheme `c.Z`, and factorization equality `c.comm`.
* Ring coefficient stages are the existing `ConstructibleExceptionalCoefficients.RingStage`:
  `.finite E n` uses `n : ℕ+` and `.integral E` uses completed coefficients. Its
  `.coefficients` selects `PurCompactSupport.finite` or `.completed` exactly.
  The field package uses a finite-dimensional extension of `Padic l`.
* `C l Ω T (s.stage l)` is the existing finite-Tor constructible category: at finite
  stages `finiteTorConstructibleCategory`, at integral stages
  `finiteTorConstructibleIntegralCategory`, including completeness and common intervals.
  `Ω : Type u` with the existing algebraic-closure instances is only the parameter of
  the shared `C` API; on both ring-stage constructors C and inclusion ignore it.
  It can always be the canonical algebraic closure; it excludes no ring-stage case.
* `RingStage.inclusion l Ω T s` is the existing full inclusion into
  `DerivedCategory (pbcModules T ((s.coefficients l).ring T))`. It uses the original
  small pro-etale site (object universe u+1, morphism universe u) and coefficient
  universe u+1, with the full inherited category; no universe equality is imposed.
* Compatible maps are `a : Change (s.coefficients l) (t.coefficients l)`. Its `map W`
  is the actual ring-sheaf morphism, and `square g` is compatibility with pullback.
  No `Allowed` witness, flatness, Tor dimension, or invertibility is imposed. Every
  composable compatible map is quantified over, as the node asks; this includes all
  allowed maps, arbitrary presentations of identity and composite ring maps, nonflat
  quotient maps, and mixed integral/finite composites.
* `H_s` is exactly the existing `image (s.coefficients l) c`: separately derived proper
  pushforward after exact open extension. `S_a^T` is `pbcDerivedExtend (a.map T)`.
  `Q_a` is `comparison a c`, the existing canonical scalar-adjunction mate of the
  proper/open restriction square, rather than an arbitrary transformation.
* The hypothesis `h W : a.map W ≫ b.map W = d.map W` records d=ba by the actual
  maps, not by an equality of allowedness proofs. Tau is the existing
  `tensorComposition (a.map T) (b.map T) (d.map T) (h T)`, whose normalized scalar
  adjunction defines balanced associativity. V is the existing `tensorIdentity`.
  For a supplied identity presentation `a`, `eqToIso (congrArg pbcDerivedExtend (h T))`
  provides the necessary transport from a.map to the actual identity map.
* `Laws.ambient_composition` is the first displayed ambient equation, expressed at
  each arbitrary ambient derived object M. Lean uses left-to-right composition:
  S_b(Q_a) then Q_b(S_a) then H_r(tau_X) equals tau_Y(H_s) then Q_d.
  This is equivalent to equality of natural transformations by extensionality.
* `Laws.ambient_identity` is Q_1 then H_s(v_X) equals v_Y(H_s), with the identity
  transport just described. Both equations live in the target ring's ordinary derived
  category, and quantify over all M, not just the finite-Tor domain.
* `Support.functor` is F_s and `Support.realization` is r_s. `Scalar.functor` is
  T_a^T and `Scalar.realization` is sigma_a^T. These are supplied isomorphisms and
  functors only. Unlike a larger existing Scalar package for another theorem, no
  exactness, commutation with shifts, right adjoint, or extra operation is required.
* `Normalized l Ω c a A B AX AY q` is exactly the displayed normalization of q,
  after translating to left-to-right categorical composition. It reads I_t(q), then
  r_t(T_a^X), then H_t(sigma_a^X), versus sigma_a^Y(F_s), then S_a^Y(r_s), then
  Q_a(I_s). It is asserted at every K in C_s(X).
* `Associator.iso` is alpha_T, and its `normalized` field explicitly says that the
  realized alpha is successive sigma followed by the canonical tensorComposition.
  `Unit.iso` is u_T; its `normalized` field explicitly says that its realization is
  sigma_1 followed by identity transport and scalar multiplication. No cocycle is an
  input field of these records.
* `Laws.composition` universally quantifies A,B,D, the six scalar realizations,
  qa,qb,qd with their three Normalized hypotheses, and alpha_X,alpha_Y with their
  realization equations. Its conclusion is precisely
  T_b^Y(qa_K) ≫ qb_(T_a^X K) ≫ F_r(alpha_X,K) = alpha_Y,F_sK ≫ qd_K.
* `Laws.identity` likewise quantifies the supplied q and the two normalized units and
  concludes q_K ≫ F_s(u_X,K) = u_Y,F_sK for every K.
* `Laws.unique` says that two specified q isomorphisms with the same actual map,
  functors and realizations and satisfying Normalized are equal. This spells out the
  last sentence's dependence only on ring maps and stated realizations. If q is indexed
  by different proofs that a map is allowed, applying this clause to the two outputs
  removes that index. When the realized presentations differ, compare them by their
  stipulated realization transports first, exactly as in the node proof Step 6.
  No inverse of the ambient Q is used or assumed.

Dependency declarations read and used:

* `Sheaf.Paper.FiniteFieldFiber`: `WeilConjectures.FiniteFieldDatum`, and its field,
  algebra and algebraic-closure instances.
* `def-weil-scheme-morphism-properties` is a convention node: use the existing Mathlib
  `Scheme`, `Over`, `IsOver`, `LocallyOfFiniteType`, `QuasiCompact`, `IsSeparated`.
* `def-sf-categories` currently records Mathlib's `DerivedCategory`, whose complete
  signature and docstring in `Mathlib.Algebra.Homology.DerivedCategory.Basic` were read.
  Its ring-stage specialization is reused through the existing C and inclusion aliases,
  not reconstructed. Those aliases are in
  `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData`, lines 48–79 and
  274–306; their full definitions were read. Although that module also contains a
  larger downstream assertion, this delivery uses only these existing definition
  interfaces, not its assertion, operation, scalar, or cocycle hypotheses.
* `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`:
  `Padic.finite_coefficientExtensionRing` and its imported finite extension, integer,
  uniformizer and quotient constructions. Positive exponents remain `ℕ+` in RingStage.
* `WeilConjectures.Compactification.RefinementCategory`:
  `AlgebraicGeometry.Compactification.Refinement` and `.category`; the recorded
  signature/docstring and imported `Compactification` structure were read. The item
  fixes one compactification and uses its original structure, not a private copy.
* `Sheaf.Paper.IntegralCompactSupportCoefficientData`:
  `WeilConjectures.PurCompactSupport.Coefficients`, `Change`, `image`, `comparison`,
  `completed`, `finite`; read the full signatures, definitions and docstrings.
* `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`:
  `PurCompactSupport.tensorComposition` and `tensorIdentity`, imported by the shared
  coefficient-data API. Their complete adjunction-normalized definitions were read.
  Existing comparison_composition and comparison_identity cover the ambient clauses
  only, not the assertion about all specified restricted comparisons.
* Proof imports, as ordinary imports: `Sheaf.Paper.RingedCoefficientPullbackCoherence`
  (`coefficientPullbackCoherence`), `Sheaf.Paper.RingedCoefficientProjectionCocycle`
  (`ringedCoefficientProjectionCocycle`), `Sheaf.SixFunctors.OpenTensorNormalization`
  (`openTensorNormalization`). Their node statements and full recorded signatures and
  proof docstrings were read. They are the three stated nontrivial proof dependencies.

Source reading: the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/def-weil-exceptional-inverse-image.md` was opened in full, together with
this item's full six-step extracted proof. This is an auxiliary scalar-normalization
statement, not the blueprint unit's own statement. The proof docstring preserves all
six steps, including the proper/open naturality interchange, cancellation through full
inclusions, unit realization and allowedness-proof independence. The older source path
in the node is retained as required; the current blueprint was used for reading.

Edge cases checked before and after writing:

* Empty X and zero K are not excluded; there is no Nonempty/nonzero hypothesis.
* j=id and p=id remain valid compactifications and the same canonical maps apply.
* a=1, b=1 and composite d expressed by any equality h remain included; tensor unit
  transports are explicit. No definitional identification of an arbitrary a with 1.
* Finite coefficient levels start at 1, never exponent 0, in the existing RingStage.
* Quotient maps such as Z/8 -> Z/4 -> Z/2 are not filtered out by flatness assumptions.
* Integral reduction followed by finite quotient, and completed extension followed by
  reduction, are quantified over as compatible Changes; no finite-only specialization.
* Nonseparated finite-type X/Y are included: only f is assumed separated.
* Ambient comparisons can fail to be isomorphisms outside C_s: the ambient clauses
  require no IsIso and the restricted clauses require only the specified q isomorphisms.
* No restriction on coefficient extension or scheme universe was imposed beyond the
  existing site coefficient size convention; all bound variables are explicit and
  `autoImplicit` is false. There is no independent smaller universe for test objects.

Searches for exact reuse (all made before writing):

* msearch.py leanfinder: "Derived compact support scalar coefficient comparisons satisfy
  composition and identity after faithful restriction". Eight hits, starting with
  CompactlySupportedContinuousMap.instIsScalarTower and supported smooth-map scalar
  comparisons; no derived sheaf comparison assertion.
* msearch.py loogle: "CategoryTheory.mateEquiv_vcomp". One hit, the general vertical
  pasting law in Mathlib.CategoryTheory.Adjunction.Mates; not this statement.
* msearch.py leansearch: "Composition and identity of compact support derived change
  of coefficients with faithful realization". Eight unrelated topological support hits,
  no match.
* msearch.py grep: "compactSupport.*[Cc]ocycle|proper.*open.*coefficient|
  coefficient.*[Nn]ormaliz". Seven unrelated Mathlib hits in vertex coefficients,
  normalized trace and tactics; no match.
* rg on lean/WeilConjectures and lean/Sheaf for
  "compactSupport.*[Cc]ocycle|comparison_comp|normalized.*[Cc]ocycle" found the ambient
  comparison_composition/identity, finite-open scalar cocycles, and the shared ring
  coefficient interfaces noted above. These were opened; none states the ambient plus
  arbitrary specified restricted normalization assertion. The existing larger
  ConstructibleExceptionalCoefficients ring system packages cocycles as output data;
  it does not supply this lemma for all realized functors/isomorphisms.
* rg on lean/WeilConjectures for the exact item id found no declaration. Final rg of
  Mathlib and both project trees for NormalizedRingCompactScalar and the main theorem
  name found no collision.

Validation: scompile.py Q60 lem-sf-normalized-ring-compact-scalar-cocycle compiled the
single delivered file in both sandbox and real library-module context, cleanly (35.7s
and 8.5s). No warnings or errors. The standard 60s per-file limit was retained. No
local Lean compiler or global build was used. No statement dispute or statement correction. The ownership-only H2 repair is recorded below.

## Second reading by Q60

The dispatcher explicitly prohibits starting other agents. This is the same worker's
separate second pass with the JSON node and final Lean file open, not a claim of an
independent agent review; the maintainer's independent review remains applicable.

I checked each displayed equation in the original node against the corresponding field
of Laws, following its source and target objects. Composition is translated consistently
to left-to-right Lean notation; qa is first mapped by BY, then qb is evaluated at AX K,
then the result is mapped by F_r(alpha_X). The right side starts at alpha_Y(F_s K).
Both ends are F_r(T_d^X K) in the same coefficient category. Identity starts with q and
ends with the normalized u_Y at F_s K. The three Normalized hypotheses contain sigma_X
on the output, sigma_Y on the input, and the two r realizations in the correct order.
The Associator.normalized field starts from inclusion(alpha) followed by sigma_d, and
its other side has sigma_b(T_a), S_b(sigma_a), then the balanced ambient tau. The unit
field includes the transport for a.map=identity before multiplication. Uniqueness compares
specified q with the same realizations and therefore covers different proofs of Allowed.

I also reread the geometric hypotheses: no absolute separatedness has appeared, the
finite-field datum and l!=p are explicit, finite type includes quasi-compactness on both
structure maps and f, and the compactification is fixed. I verified finite versus integral
C and inclusion branches, including positive-level and completed-sheaf conventions. The
ambient fields quantify arbitrary ordinary derived inputs; the restricted fields quantify
only K in the shared finite-Tor categories. The input-only records deliberately omit the
stronger existing Scalar package's exactness and shift fields, which would add hypotheses
not present in this node. No further mismatch was found and no statement correction was
needed. The final module contains one named sorry theorem and concrete definitions only.


## Repair of H2 at immutable head c7ea036e9a72

L verified the mathematical statement clause by clause and returned only missing
statement-dependency ownership. This packet repairs every part of that finding:

1. Added `def-sf-ring-scalar-multiplication-unit`, an existing:true definition node
   recording `WeilConjectures.PurCompactSupport.tensorIdentity` and
   `WeilConjectures.PurCompactSupport.restrictIdentity_existsUnique` in
   `Sheaf.Paper.IntegralCompactSupportCoefficientComparison`. The item cites it in
   stmt_deps. This accounts for tensorIdentity in Unit.normalized and ambient_identity.
   The new node describes the exact definition: take the unique sectionwise-identity
   ordinary scalar restriction isomorphism, derive it, and conjugate using the actual
   scalar adjunction and the identity adjunction. The uniqueness theorem has an actual
   proof in the published source; the definition is concrete, with no new sorry.
2. Added the landed definition `def-pur-finite-compact-support-scalar-data` to stmt_deps.
   Its recorded declarations include the tensorComposition used in Associator.normalized
   and ambient_composition. Its complete statement and lean record were reread.
3. Added the landed definition `def-weil-exceptional-inverse-image` to stmt_deps.
   Its recorded definitions include FieldStage, Stage, C, category, RingStage, stage,
   coefficients and inclusion, which the delivered module uses. Its complete statement
   and lean record, and the defining signatures/docstrings in
   ConstructibleExceptionalAdjunctionCoefficientsData, were reread. No System value
   or existence theorem is assumed by this item.

No theorem has been added to the item's stmt_deps. In particular the item does not
cite lem-pur-compact-support-integral-coefficient-comparison or
lem-sf-constructible-exceptional-adjunction-coefficients as a statement dependency.
Importing an existing module to access those definition owners adds no theorem premise.
The mathematical statement, proof plan, proof_deps, and Lean source are unchanged.
The module SHA256 remains
`d6cfbc1856026a49b533712f8650c58694d4e6d02fac42f465a952337fd9e217`.

The sandbox node was compared to current main before rebasing the metadata: it differed
only in lean, matching the returned packet. The repaired node preserves every current
main field outside lean and the three appended stmt_deps. The delivery wrapper builds
its replacement commit on current origin/sheaf-dag; no direct git command is used.

## New nodes

`def-sf-ring-scalar-multiplication-unit` owns the previously theorem-only-recorded
multiplication-normalized identity derived scalar comparison, including its unique
ordinary identity-section restriction isomorphism. It reuses the exact existing
`tensorIdentity` and `restrictIdentity_existsUnique` declarations; there is no new
module, renamed constant, copied definition, or new theorem. Source: Stacks
sites-cohomology.tex, Tags 06YY (derived scalar pullback) and 07A6 (derived adjunction),
specialized to the identity ring map, with the existing normalization in
IntegralCompactSupportCoefficientComparison. The cited source lemmas and the complete
existing definitions/docstrings were opened. The new node cites the existing definitions
of the small pro-etale site, module category, ordinary derived category and the
BoundedConstructibleTower scalar operations (pbcModules, pbcRestrict, pbcDerivedExtend,
pbcDerivedScalarAdjunction). Those four dependencies are all definition nodes.

The new node's mathlib_searches record the repair searches and their results:
LeanSearch returned ordinary scalar-unit lemmas (including
ModuleCat.extendScalarsId_hom_app_one_tmul); LeanFinder returned ordinary pullback and
restriction identity comparisons; Mathlib grep returned 18 ordinary AlgCat/ModuleCat
matches. Project grep found the exact published pro-etale derived construction and its
consumers. DAG grep found tensorIdentity only in the theorem record; the occurrence of
restrictIdentity_existsUnique on def-sf-open-reduction-coefficient-mate is historical
sorry_before metadata, not definition ownership. blueprint_refs.py searches for
“tensorIdentity” and “scalar multiplication unit” returned zero nodes. Thus this is a
missing definition owner attached to an existing construction, exactly as L requested.
The id did not exist on main when created. Its chapter and unit equal the item's, and
blueprint.from.via prepends the item to its existing chain. blueprint_refs.py ancestor
reports None for this item's inherited chain, so the new record preserves that result.

## Second reading by Q60 — repair

No other agent was started, as the dispatcher prohibits it. In a separate reading I
checked the new node against the two existing declarations: W is any Scheme.{u}; R is
any commutative ring sheaf in universe u+1 on the original small site; the ordinary
comparison is uniquely sectionwise identity, and the derived comparison is precisely
its conjugate with the displayed final symm. This gives the claimed direction
pbcDerivedExtend (identity R) to identity, matching both unit occurrences in the item.
Finite, completed, zero, empty-site, and arbitrary unbounded derived inputs are retained.
There is no flatness, constructibility or mate-invertibility hypothesis in the new node.
The recorded lean.statement is the exact tensorIdentity signature through the colon
and result type, stopping before :=. The lean.declarations list includes its uniqueness
helper as requested. The two other new statement dependencies are landed definitions
with precisely the required declarations. Only metadata changes; the earlier reviewed
Lean equations, hypotheses, universe parameters, and edge cases remain byte-identical.

Repair validation: scompile.py again accepted the unchanged delivered module in both
sandbox and library contexts with no diagnostics. deliver2.py --no-push then compiled
the delivered module and a generated probe for both existing declarations, and printed
`OK (dry run): commit ed884f305bf passes the preflight and compiles; nothing pushed`.
Local metadata checks confirmed the new node's bracketed citations equal stmt_deps,
tensorIdentity's signature is verbatim, and the item differs from current main only in
lean and stmt_deps. No read-only source or launcher tool was edited.
