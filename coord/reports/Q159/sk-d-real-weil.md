## Worker report

The delivery supplies `Sheaf.Paper.RealWeilSheaves`. Its main declaration is
`RealSheaves.ConstructibleWeilSheaf`. It also states the finite-model criterion and
supplies the literal every-basis lissity predicate, including infinite bases and
independent coefficient and vector universes. Existing definitions are retained
for the Weil group, its degree and topology, local Frobenius, actual étale lisse
Weil pairs, and their stalk representations. No theorem is proved in this file.
The two theorem bodies are `sorry`; every definition has actual data.

The node has not been corrected. Its only changes are `lean` and addition to
`stmt_deps` of the already published `def-weil-algebraically-closed-coefficients`.
That dependency supplies the canonical small finite-field models inside the chosen
closure; it avoids any equation between the site and closure universes. There are
no new nodes and no dependency-node replacements.

Clause-by-clause reading:

1. The curve and coefficient conventions are precisely `RealSheaves.Setup` and
   `Setup.IsCurve`, from `Sheaf.Paper.RealSheavesSetup`. The geometric fibre is
   literally `Setup.geometricCurve`. `Setup.weilFieldDatum` merely repackages the
   same p, a, q, k0 and k into the existing `FiniteFieldDatum`; it chooses no new
   field. Its cardinality proof is `Nat.card_eq_fintype_card.trans D.card_eq`.
   The coefficient prime and its inequality are retained by the parameter D.
   `ConstructibleWeilSheaf` takes exactly `(hC : D.IsCurve C₀)`.
2. The finite-étale fibre functor is
   `AlgebraicGeometry.Scheme.FiniteEtale.fiber`. The other recorded interface,
   `Scheme.flcFiber` from `Sheaf.AlgebraicGeometry.FundamentalGroup.FLCFiber`,
   is publicly reexported through the existing dependency imports, with the
   existing finite-étale/FLC comparison. No second stalk or fundamental group is
   defined. The scheme-side notion here is the finite-étale one stated in the node.
3. `Scheme.FiniteEtale.weilGroup p s G` is the existing subgroup of
   `G × Multiplicative ℤ` characterized by its constant-cover Frobenius action.
   `WeilGroup.ofFundamentalGroup` constructs the existing curve Weil group from
   that subgroup. Its `weilGroupEquiv`, `deg_eq` and `deg_surjective` fields give
   exactly the arithmetic presentation and the surjective degree map.
   The abstract fundamental-group model is equipped with
   `PreGaloisCategory.IsFundamentalGroup (FiniteEtale.fiber s) G`, not an
   unrelated group. All representation statements use that existing `WeilGroup`.
4. The exact sequence is encoded by the existing `W.deg` and its kernel
   `W.geometric`. The underlying subgroup exact sequence is
   `MonoidHom.exact_weilGroupDeg`. The geometric fundamental-group identification
   is the existing `WeilGroup.EtaleQuotientData`/`IsEtaleQuotient` interface in
   `WeilConjectures.EtaleCohomology.Purity.RealSheaves.FundamentalGroup` and the
   arithmetic exact-sequence dependency. No exactness assertion is replaced by
   an arbitrary injection or by a hypothesis about a different group.
5. The topology is the existing Weil topology, not the topology of a subgroup of
   G alone. In `WeilGroup.ofFundamentalGroup` it is the topology of the subgroup
   of `G × Multiplicative ℤ`, with the integer factor discrete. An arbitrary
   presented W has `isOpen_ker` and `isEmbedding_ker`; `W.toStandard` is the existing
   topological group equivalence to this standard product-subgroup model.
   Compactness and total disconnectedness of the geometric kernel are retained.
6. A representation uses Mathlib `Representation Q W.carrier V`. For a group,
   this is equivalently a homomorphism to invertible linear maps, via
   `Representation.asGroupHom` and `GeneralLinearGroup.generalLinearEquiv`.
   There is no replacement of GL(V) by arbitrary noninvertible endomorphisms.
7. `W.IsLisseInEveryBasis l Q ρ` binds the coefficient closure Q, endowed with
   `spectralNorm.nontriviallyNormedField ℚ_[l] Q`, and quantifies over every
   `(ι : Type w) (b : Module.Basis ι Q V)` and `(i j : ι)`. Its coefficient is
   `b.repr (ρ g (b j)) i`, and the domain is exactly `g : W.geometric`.
   Thus the definition includes infinite-dimensional V and arbitrary bases. The
   pre-existing `W.IsLisse` quantifies only over bases indexed by `Fin n`; it
   would be vacuous in infinite dimension. It is consequently not an exact
   existing declaration for this general clause. The named compatibility theorem
   `isLisse_iff_everyBasis` identifies the two predicates in finite dimension.
8. The lisse étale adic sheaf and its global Weil isomorphism are the existing
   `Scheme.EtaleLisseWeilSheaf l Q h`, namely
   `Endofunctor.IsoAlgebra (lisseAlgebraicAutomorphismPullback h l Q)`.
   Its carrier belongs to the dependency's actual `LisseAlgebraicSheaf`, with
   its integral systems, rational Hom and common coefficient construction.
   Here h is geometric Galois Frobenius. `D.weilFrobenius C₀ hC` is precisely
   `id × Spec(z ↦ z^(1/q))`, through the existing finite-field datum construction,
   on the literal fibre `D.geometricCurve C₀`. It uses the finite-type components
   of hC directly; there is no extra assumption or arbitrary automorphism.
9. The stalk Weil representation remains
   `Scheme.etaleFundamentalRep`; its finite-cover germ normalization, inverse
   limits, rationalization, path transport and degree-one operator are unchanged.
   Its argument `EtaleWeilDegreeData` gives the prescribed lift/path convention,
   and `WeilMonodromyData.toEtale` is the existing curve adapter. In particular,
   this delivery does not substitute a pro-étale representation. The equivalence
   of lisse sheaves with representations is the pointer to
   `prop-wf-weil-sheaf-representation-equivalence` specified in proof step 4 of
   the node. Importing or using that downstream theorem to define these objects
   would close a cycle, so no such import or dependency is added.
10. `isLisse_iff_finiteModel` has the required finite-dimensional hypothesis
    `[FiniteDimensional Q V]`, and its left side is the general lissity predicate.
    The right side chooses an intermediate field E of Q with
    `FiniteDimensional ℚ_[l] E`, an integer n, a Q-basis b of V, and a representation
    `σ : Representation E W.carrier (Fin n → E)` of the WHOLE Weil group.
    Its matrix equality for EVERY w identifies scalar extension of σ with ρ.
    The E-action is continuous on the geometric kernel: its matrix entries are
    continuous for E's spectral topology. In finite dimension this is the same
    joint continuity as `Representation.IsContinuousCoefficient`.
11. The lattice is a `Submodule (Padic.coefficientExtensionIntegers l E)
    (Fin n → E)`, with a basis indexed by `Fin n`, and with E-span equal to top.
    This is literally a free integer lattice of the required rank and full span,
    including rank zero. The only stability quantifier is
    `(g : W.geometric) (x : Λ)`. No condition is imposed on σ at degree one.
12. A degree-one lift is already `W.frobeniusLift`, with
    `W.deg_frobeniusLift`. The expression called F is `ρ W.frobeniusLift`.
    Other lifts may be used with the dependency's lift-change theorem; there is
    no redundant definition of evaluation of a representation at an element.
13. Local Frobenius is the existing `W.frobenius x`. Its
    `isFrobeniusElement_frobenius` field uses exactly the residue Galois action on
    finite-étale fibres transported along a path, not an arbitrary element of the
    right degree. `deg_frobenius` gives the residue degree. The existing
    `WeilGroup.isConj_frobenius_of_isFrobeniusElement` and
    `FiniteEtale.IsFrobeniusElement.exists_mem_weilGroup_conj` give conjugacy
    inside W for alternative residue paths. `WeilGroup.weilFrobenius` is the
    standard subgroup representative of the same construction.
14. The constructible pair is `RealSheaves.ConstructibleWeilSheaf D C₀ hC`.
    Its `coefficient` is one finite subextension of D.Qbar. Its `integral` field
    is ONE global `AdicIntegralDiagramOfUniverses` on the geometric curve.
    `IsConstructibleWeilDiagram` requires a single finite locally closed scheme
    stratification S of C₀. For each i it restricts this same system along
    `pullback.snd (S.immersion i) (pullback.fst ...)` to
    `Z_i ×_(C₀) C`, canonically the geometric fibre of that stratum, and applies
    the recorded `IsLisseIntegralDiagramOfUniverses` there. The dependency
    predicate includes finite local constancy at every positive level,
    annihilation by the uniformizer power, and the stalk reduction-isomorphism
    criterion. Since the strata cover, these annihilation and reduction conditions
    also hold globally. Every finite level is a constructible finite quotient-ring
    sheaf in the sense of `IsConstructibleEtaleModuleSheaf`: on this same finite
    stratification it has finite locally constant values. Finiteness as sets follows
    from finite generation and annihilation over the finite positive-level ring.
15. `weilDiagramDenominators` inverts uniformizer powers times isomorphisms of
    global diagrams. Its ordinary category localization has the same objects,
    rationalized Hom, and kills bounded uniformizer-torsion. These are the
    rationalized global systems of Weil II (1.1.1)c. `frobenius` is an actual
    isomorphism there from the rationalized global pullback to the rationalized
    integral system. It is not an integral isomorphism: in particular a degree-one
    scalar with nonzero valuation is allowed.
16. The finite-field-of-coefficients convention is realized by the `coefficient`
    field and its existing canonical small `Coefficient.{u}` model. A Weil pair
    and its inverse isomorphism descend to one finite coefficient field, after
    adjoining finitely many coefficients if necessary; thus a common-field
    representative loses no object. As in the dependency's coefficient-pair
    presentation, different models are not identified by equality. This item
    defines the objects/pairs, not a new scalar-extension or Hom theory for them.
    There is one global sheaf/system and one global Weil isomorphism. The strata
    occur only in a Prop witness and cannot supply independently chosen sheaves.

Additional dependency declarations read and used: the coefficient constructions
`Padic.coefficientExtensionIntegers`, `coefficientExtensionUniformizer`,
`coefficientExtensionIdeal`, and `finite_coefficientExtensionRing` from
`Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`; the finite local-constancy
and exact etale pullback interfaces reexported by the lisse dependency;
`Scheme.FiniteLocallyClosedStratification` from its recorded module; and
`AlgebraicallyClosedCoefficients.Index`, `Coefficient`, `coefficientSmall` and
`coefficientFinite` reexported by
`Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`.

All available recorded proof-dependency modules are imported without `public`:
ArithmeticLiftFibrePath, AutProfinite through the fibre interface,
ProfiniteStableLattice, the exact existing compact-matrix descent theorem
`PadicAlgCl.exists_finiteDimensional_forall_mem` in IntegralModel,
FibreFunctorBasepointTransport, fundamental-group Functoriality through the group
module, and FiniteFieldAbsoluteGalois. The finite-field Frobenius Mathlib leaf is
already reexported. The proof docstrings explain the finite-model criterion in
both directions, including isometric transport from an arbitrary coefficient
closure to the canonical closure for compact matrix descent, and its finite-basis
compatibility.

Edge cases checked before writing and on rereading: V=0 and n=0 (empty bases,
zero full lattice); infinite-dimensional V (the every-basis predicate is not
vacuous); E=ℚ_l and identity coefficient models; arbitrary independent universes
for D.Qbar and the geometric curve, and for representation V; disconnected or
empty strata (allowed by the existing stratification); a rank-one degree-one
operator equal to a uniformizer (allowed, its inverse exists rationally);
changing degree-one lift; local Frobenius of degree greater than one; changes of
residue path (conjugacy must be in W, not merely in the arithmetic group).
The curve itself is nonempty by the stated hC, rather than an added assumption.

Searches made:

- `msearch.py ... leanfinder "lisse Weil sheaf continuous representation geometric
  fundamental group constructible adic sheaf"`: eight condensed-module results;
  none supplied this statement.
- `msearch.py ... loogle '"WeilGroup"'`: zero Mathlib hits.
- `msearch.py ... grep 'WeilGroup|WeilSheaf|WeilRepresentation'`: zero Mathlib hits.
- `msearch.py ... leansearch "constructible adic sheaf compatible inverse system
  rationalization Weil Frobenius isomorphism"`: eight isocrystal/adic-completion
  results; none defined constructible Weil pairs on this site.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for Weil groups, lisse Weil
  sheaves, constructible adic systems and the proposed declaration names, plus
  `rg -n sk-d-real-weil lean/WeilConjectures`: found and read the exact existing
  curve group in RealSheaves.Basic/Construction, local Frobenius and conjugacy,
  and the lisse etale dependency. Those are reused. The ordinary-sheaf
  `IsConstructibleEtaleModuleSheaf` is only a finite-ring predicate. The existing
  `WeilSheaf` uses pro-étale coefficients; `sfCommonStageWeilSheaf` uses an
  intrinsic derived constructible heart. Neither is the actual compatible étale
  system with the source's given lisse-étale convention, without an additional
  comparison. They are not silently substituted. No existing declaration
  supplies the added global compatible-system pair or the entire finite-model
  criterion with a WHOLE-Weil E-model and geometric-only lattice invariance.
- Opened the current blueprint unit and Weil II pp. 146--147, especially
  (1.1.1)b--d: constructible systems, rational Hom, torsion quotient and common
  coefficient fields. The integral stratum condition agrees with the stratified
  lissity statement referenced there (SGA 5 VI (1.2.6)).

No `STATEMENT-DISPUTED` issue remains. The old finite-basis interface's behavior
in infinite rank was addressed by a distinct, genuinely more general interface,
with the finite-dimensional compatibility stated explicitly.

Validation: the current module compiled cleanly through scompile.py in both its
sandbox and named-library modes (27.3 s and 31.9 s), with no error or unexpected
warning. An earlier variant's named compile exceeded 60 s; it was superseded by
the current cleanly compiled source. No local or global build was run directly.

## Second reading by Q159

I reopened the node, the generated module, and the recorded dependency signatures
and made a separate clause-by-clause pass. This is the worker's own second pass;
the independently reviewing maintainer is the independent reader specified in the
brief, and no second agent was started.

The pass found two issues and repaired them: the initial use of the existing
finite-basis lissity predicate did not cover the node's arbitrary-dimensional
initial representation; the new every-basis predicate includes it. Also the first
finite-model theorem specialized Qbar and the vector universe to the upstream
canonical closure/curve universe; the final theorem allows independent u, v, w
and any algebraic coefficient closure. The compatibility theorem retains the
existing canonical-closure interface for its actual consumers.

I checked that the global constructible pair has exactly one system and one global
rational Frobenius isomorphism, that the existential S is on C₀ and its restrictions
are on geometric fibres, that every transition belongs to the same pulled-back
system, and that scalar localization allows nonintegral degree-one action. In the
finite-model criterion σ acts on all of W, while continuity and invariance quantify
only over W.geometric. Its basis and full-span clauses give exactly the lattice
rank and spanning requirement; no finite-rank case or zero-dimensional case is
lost. The existing local-Frobenius field specifies the residue/path action and
its existing conjugacy theorem conjugates in W. No statement text was changed,
no downstream equivalence was used to define its own objects, and no comparison
between pro-étale sheaves, derived hearts and the actual étale systems was assumed.

The required deliver2.py --no-push dry run returned OK: its server preflight
and per-file compilation passed. The final push is through deliver2.py only.
