## Worker report

The item is stated by the existing declaration
`WeilConjectures.finiteCoefficient_derivedHom_ctf_etale` in
`lean/Sheaf/Paper/EtaleHomFiniteTorAmplitude.lean`, module
`Sheaf.Paper.EtaleHomFiniteTorAmplitude`. No module is added to this delivery.
The declaration is an exact Lean rendering of the node's finite-stage étale
internal-Hom assertion.

The declaration's hypotheses render every clause of the node statement as
follows. `D : FiniteFieldDatum`, `l` prime with `_hl : l ≠ D.p`, and
`E` finite-dimensional over `Padic l` provide the fixed coefficient datum;
`n` and `hn : 1 ≤ n` provide `A = A_{E,n}`. The scheme hypotheses
`X : Scheme`, `[X.Over (Spec (.of D.k))]`,
`[LocallyOfFiniteType ...]`, and `[QuasiCompact ...]` give a finite-type
scheme over the algebraic closure, while `m` and `_hm` give the dimension
bound. Ordered integer endpoints are rendered by `_hab : a ≤ b` and
`_hcd : c ≤ d`. The two complexes `K M` are objects of the finite
coefficient étale derived category, and `_hK`, `_hM` render bounded
constructibility with finite Tor amplitude. The conclusion is the conjunction
of finite-Tor bounded constructibility for the derived internal Hom, the
interval `[c-b-2m,d-a+2m]`, and the implication from
`Etale.DerivedCategory.IsSitePerfect K` to the sharper interval
`[c-b,d-a]`.

Dependency declarations used are the recorded declarations of the existing
node: `Sheaf.Paper.FiniteFieldFiber` (`FiniteFieldDatum`),
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
(`Padic.coefficientExtensionRing`), `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
(`LocallyOfFiniteType`), `Mathlib.Topology.KrullDimension`
(`topologicalKrullDim`), `Mathlib.AlgebraicGeometry.Sites.Etale`
(the étale derived category), `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`
(`finiteTorConstructibleEtale`), and `WeilConjectures.SixFunctors.Etale.Derived.Hom`
(`Etale.derivedHom` and `hasTorAmplitudeIn`). The exact theorem itself is
already reviewed in `dag/nodes/sec-six-functors/thm-sf-hom-ctf.json` and does
not cite this item.

Edge cases checked from the reviewed proof and statement: the empty scheme
uses the empty affine cover; zero complexes satisfy both Tor windows; at
`m = 0` the general endpoints reduce to the sharper endpoints; and the
site-perfect implication is conditional, so no unsupported perfectness is
added to the general clause. The theorem retains the geometric `2*m` shift
for general internal Hom.

Searches made before selecting the existing declaration: `msearch.py Q114
sk-thm-sf-hom-ctf leanfinder` for derived internal Hom of bounded
constructible étale complexes with finite Tor amplitude; `msearch.py ...
leansearch` for the same assertion; `msearch.py ... loogle` for
`CategoryTheory.ihom`; and `msearch.py ... grep` for
`torAmplitude|derivedHom|constructibleFiniteTor` and for internal-Hom names.
The semantic searches returned only generic category/cohomological results,
and the Mathlib greps returned no constructible étale Tor-amplitude theorem.
A project search found the exact declaration above, whose full signature and
docstring were read. Therefore the node's `lean` record sets `existing: true`
for that declaration; there are zero new nodes and zero Mathlib leaves.

## Second reading by Q114

I independently read the sandbox node, the existing theorem's full signature and
proof docstring, the exact main-20261015 `_section.md` and
`sk-thm-sf-hom-ctf.proof.md`, and the section's coefficient conventions. The source
of this item is the blueprint, not a Stacks theorem; its proof explicitly works
on the small etale site at finite coefficients. I also read every statement
dependency's natural statement and recorded signature, and opened the relevant
Lean definitions. Current upstream sources absent from the older checkout were
read with `scompile.py --source` (SitePerfect, Coefficients, Hom, and
BoundedConstructibleComplexes).

Verdict: the worker's existing binding is not exact. It excludes negative integer
dimension bounds, a case explicitly retained in the node's reviewed proof. I
replaced that binding with the new module
`Sheaf.Paper.EtaleHomFiniteTorAmplitudeIntDimension`, declaration
`WeilConjectures.finiteCoefficient_derivedHom_ctf_etale_intDimension`. The worker
report above describes the original proposal; this section supersedes its claim
of exactness and of zero delivered modules. The mathematical node statement,
proof, and dependency lists are unchanged. There is no statement correction,
new definition node, or dependency module.

The statement inventory and final Lean correspondence are:

1. Global finite-field datum, understood throughout the source: `D :
   FiniteFieldDatum.{u}`. I read its fields: prime p, positive exponent, cardinality,
   finite base field, and fixed algebraic closure with its algebra structure.
   Verdict: exactly the global datum, with arbitrary chosen algebraic closure.
2. Coefficient prime distinct from the characteristic: `l : ℕ`, `[Fact l.Prime]`,
   `_hl : l ≠ D.p`. Verdict: exactly the coefficient convention, without an extra
   characteristic restriction.
3. Finite extension E of Q_l and coefficient ring A at positive level n:
   `E : Type u`, `[Field E]`, `[Algebra (Padic l) E]`,
   `[FiniteDimensional (Padic l) E]`, `(n : ℕ) (hn : 1 ≤ n)` and
   `ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n)`. I read the quotient
   construction: the valuation ring modulo the nth power of the uniformizer ideal.
   The lift only changes size, retaining the coefficient ring. Verdict: exact.
4. Finite-type k-scheme: `X : Scheme.{u}`, `[X.Over (Spec (.of D.k))]`,
   `[LocallyOfFiniteType (X ↘ Spec (.of D.k))]`, and
   `[QuasiCompact (X ↘ Spec (.of D.k))]`. I opened both Mathlib classes; their
   conjunction is precisely finite type. No separatedness, smoothness, or
   additional Noetherian assumption is imposed. Verdict: exact.
5. Integer dimension bound: `(m : ℤ)` and
   `_hm : topologicalKrullDim X ≤ if m < 0 then ⊥ else
   (m.toNat : WithBot ℕ∞)`. Mathlib dimension has values bottom, nonnegative
   integers, and infinity. Thus for m negative the displayed comparison says
   dimension is bottom, exactly the condition dim X ≤ m; for m nonnegative it
   says dim X ≤ m.toNat. The original `(m : ℕ)` omitted the former case.
   Verdict: repaired, with no positivity hypothesis added.
6. Tor intervals: `(a b c d : ℤ)`, `_hab : a ≤ b`, `_hcd : c ≤ d`.
   The node's finite-Tor definition uses ordered finite intervals. Verdict: exact.
7. Objects and site: `K M : Etale.DerivedCategoryModule
   (ULift ... (Padic.coefficientExtensionRing l E n)) X`. This is the unbounded
   derived category of module-valued sheaves on `X.smallEtaleTopology`, whose
   objects and jointly surjective covers I checked in Mathlib. It is the etale
   finite-coefficient category, without an integral, condensed, or pro-etale
   replacement. Verdict: exact.
8. Bounded constructibility and finite Tor amplitude: `_hK`, `_hM` are
   `finiteTorConstructibleEtale l E n hn X K/M`; `_hKt`, `_hMt` are
   `hasTorAmplitudeIn ... X a b K` and `... X c d M`. I opened the former
   definition: recorded finite-value bounded constructibility together with
   existence of an ordered Tor interval. I opened the latter: all module sheaves
   in degree zero are tested for derived tensor cohomology vanishing outside the
   specified interval. The existence clauses add no stronger assumption once the
   displayed ordered windows are supplied. Verdict: exact.
9. Derived internal Hom: `((Etale.derivedHom (ModuleCat ... A) X).obj
   (op K)).obj M`. I read its definition and adjunction: the internal Hom right
   adjoint to the derived sheaf tensor product. This is the etale presentation of
   the recorded ringed-site derived internal Hom, not global Hom/Ext and not the
   Hom of stalks. Verdict: exact.
10. General conclusion: first conjunct `finiteTorConstructibleEtale ... RHom`,
    second conjunct `hasTorAmplitudeIn ... X (c - b - 2 * m)
    (d - a + 2 * m) RHom`. All bounded-constructible and finite-Tor clauses and
    both endpoints are retained. Verdict: exact, now also for signed m.
11. Sharper conditional conclusion: `Etale.DerivedCategory.IsSitePerfect K →
    hasTorAmplitudeIn ... X (c - b) (d - a) RHom`. I read the predicate's actual
    data: an etale cover, bounded complexes on its members, every term a retract
    of the constant sheaf of `Fin r → A`, and an isomorphism to the derived
    restriction of K. These are finite-projective sheaf models, not arbitrary
    projective objects or merely perfect stalks. The source's proof explicitly
    explains that a perfect complex with Tor amplitude [a,b] admits those models
    in [a,b]; `lem-sf-site-perfect-tor-window` states that implication and its
    declaration was opened. Forgetting bounds proves the reverse implication.
    Thus with hypothesis 8 this existing predicate is equivalent to the source's
    bounded-model condition. It does not assume perfectness for the general
    clause. Verdict: exact, with the same quantifier/implication order.

Dependency-interface audit: the finite-field and coefficient constructions are
reused directly. The current finite-Tor dependency record publicly retains
`FiniteTorAmplitudeSites`, so its etale predicate remains the applicable
presentation. The constructibility dependency now lives under
`WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`; I read the
current source, which uses the recorded finite-value constructibility predicate,
not upstream `boundedConstructible` with a different constructibility interface.
The general ringed-site strict-perfect package and derived-Hom dependencies
serve the same notions; this specialized etale statement uses the already
published etale interfaces from the existing theorem's import closure. The
separate `def-weil-site-perfect-complex` record is for the pro-etale coefficient
stages and is not substituted for the etale predicate. No private definition,
new construction, hollow datum, or dependency repair is needed.

Edge cases: the empty scheme is allowed for every m, including m < 0. Then
all sheaves and derived objects vanish because the empty covering family forces
zero sections; the conclusions hold even when the general interval reverses.
Zero K or M is allowed. At m = 0 the two displayed windows agree. n = 0 is
excluded exactly by the source's coefficient convention n ≥ 1, not by a hidden
instance. The characteristic restriction is exactly l ≠ p. Empty etale covers
and rank-zero finite-free retracts are included by the existing predicate.
No independent index universe or Nonempty hypothesis is added. The universe u
is arbitrary; the scheme, fields, and finite quotient can be put in a common
universe, and the canonical coefficient ULift supplies the u+1 etale module
universe. There is no equality forced between unequal site universes.

Independent searches (fresh wording, through the prescribed wrapper):

- LeanFinder: “Derived sheaf Hom preserves constructibility and flat dimension
  with an integer dimension bound including the empty scheme”. Eight results
  about flat morphisms and the abelian category of scheme modules, no theorem.
- LeanSearch: “Derived internal Hom of finite Tor constructible etale complexes
  with signed dimension upper bound”. Eight results about derived categories,
  orthogonality, Ext size, and tensor signs, no theorem.
- Loogle: `topologicalKrullDim`. Seven results; checked the dimension signature
  and monotonicity/equality statements, none supplies this Hom theorem.
- Direct rg of Mathlib Algebra/Homology and AlgebraicGeometry for `derivedHom`,
  Tor-amplitude names and constructible-Hom combinations: only constructible
  subsets/images of scheme morphisms, no sheaf-Hom theorem.
- Direct rg of the upstream WeilConjectures tree and project lean/Sheaf for
  derived-Hom stability and the proposed declaration name. Opened the upstream
  `Stability/DirectImage.lean` declarations: their dimension parameter is also
  natural and their bounded-constructibility predicate differs from the recorded
  finite-value predicate. The exact node is therefore not an existing match.
  The project theorem selected by the worker is the correct nonnegative-bound
  prerequisite, not a replacement for the signed-bound statement. No collision
  with the new declaration name was found.

Repair and conventions: the new module has only the node's named theorem with
whole proof `sorry`; no definitions or proved helpers. Its module/theorem
source docstrings carry `(blueprint: sk-thm-sf-hom-ctf)`. Its proof docstring
spells out the node's negative-bound empty-scheme argument, application of
`thm-sf-hom-ctf` at m.toNat, and the site-perfect clause. The proof dependency's
module is imported. All variables and the universe are explicitly bound;
there is no file-local notation or instance, and lines are at most 100 columns.
The node's lean.statement was extracted verbatim (normalized whitespace) from
the delivered theorem signature. `scompile.py Q114 sk-thm-sf-hom-ctf
lean/Sheaf/Paper/EtaleHomFiniteTorAmplitudeIntDimension.lean` compiled both
sandbox and library forms cleanly, with no errors or warnings (1.9 s and 2.1 s).
