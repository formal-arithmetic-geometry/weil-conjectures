## Worker report

The module `Sheaf.Paper.DerivedNakayama` states
`AlgebraicGeometry.ProEtale.DerivedNakayama.reduction_and_derived_nakayama`.
Its only proof is `sorry`. There are no new definitions, copied notions, dependency
repairs, or statement changes. The theorem packages all sentences of the unit statement.

Hypotheses and clauses, checked against the node and its current main-20261015 source:

- The finite extension E/Q_l is `(l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]`. The uniformizer is the
  dependency's chosen `Padic.coefficientExtensionUniformizer l E`.
- The integral coefficient is `AdicCompletion.ring l E X`, definitionally
  `condensedRingObj (integerRing l E) X`. Its internal module category is
  `AdicCompletion.Modules l E X`. These are the continuous condensed coefficients,
  pulled back by `upperStarFromPoint X`, rather than constant integral sheaves.
  Schemes are arbitrary `X : Scheme.{u}`; there is no finiteness or characteristic
  hypothesis on X.
- Positive finite levels are indexed by `n : ℕ`, with mathematical exponent `n + 1`.
  Thus the first finite coefficient is `AdicCompletion.finiteModule l E X 0`.
  This indexes every positive exponent, including exponent one.
- The first conjunct supplies an endomorphism `d` of the regular integral module on
  the point. The equation quantified over profinite S, continuous section f and
  point s identifies its underlying map exactly with multiplication by pi_E.
  This is a characterization, not an arbitrary scalar map assumed as a hypothesis.
- The perfect resolution is expressed by its actual defining finite free witness:
  `∃ P`, with `P.IsStrictlyGE (-1) ∧ P.IsStrictlyLE 0`, and isomorphisms `em` and
  `e0` from its terms in degrees -1 and 0 to `Mod.regular (AdicCompletion.ring l E X)`.
  Every other term is zero. The displayed differential equation, transported along
  those isomorphisms and `regularPullbackIso`, is precisely multiplication by
  `pi_E^(n+1)`. The augmentation `ε` goes to the single complex of the actual
  finite coefficient, satisfies `QuasiIso ε`, and its degree-zero component is
  `e0.hom ≫ AdicCompletion.finiteUnit l E X n`, the canonical quotient map.
  This explicitly states the claimed bounded finite free resolution; its terms
  have the identity rank-one splittings on the identity covering, hence it is
  perfect in the cited ringed-site sense. No alternate perfectness predicate is
  introduced, and perfectness is not weakened to an unspecified representative.
- The cone sentence is the natural isomorphism
  `DerivedCategory.Q ⋙ reductionFunctor l E X (n+1) ≅ coneFunctor l E X (d^(n+1))`.
  `coneFunctor` is the already recorded standard mapping-cone functor, including
  its functorial maps. Thus every representative C of K has the stated cone;
  the natural comparison also asserts that this model descends to the derived
  category. `reductionFunctor` is precisely derived tensor with the finite
  coefficient in degree zero, retaining the integral scalar action.
- The vanishing sentence is the second main conjunct, quantified over all X and
  all `K : Derived l E X`: `IsDerivedComplete l E X K →
  IsZero ((reductionFunctor l E X 1).obj K) → IsZero K`.
- The final sentence is the last conjunct, quantified over all X, K, L and
  `f : K ⟶ L`: completeness of both objects and
  `IsIso ((reductionFunctor l E X 1).map f)` imply `IsIso f`.
  The same reduction functor is used on objects and morphisms.

Dependency declarations read and reused:

- `Sheaf.SixFunctors.ProEtale.DerivedCompletion`:
  `AlgebraicGeometry.ProEtale.IsDerivedComplete` and
  `AlgebraicGeometry.ProEtale.AdicCompletion.ring`, `Modules`, `finiteModule`,
  `finiteUnit`. Completeness is the recorded K-flat Roos augmentation criterion;
  no alternate or merely objectwise isomorphic completion is substituted.
- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
  `AlgebraicGeometry.ProEtale.coefficientRing`, `condensedRingObj`,
  `upperStarFromPoint`, and the commutative ring-object transport instance.
- `Sheaf.Paper.DerivedNakayamaResolution`: namespace
  `AlgebraicGeometry.ProEtale.DerivedNakayama`, in particular `integerRing`,
  `pullback`, `regularPullbackIso`, `Derived`, `reductionFunctor`, and
  `coneFunctor`. Its `derived_nakayama_resolution` is a proof dependency.
- The proof-only imports are `Sheaf.Paper.DerivedNakayamaResolution`,
  `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
  (`AlgebraicGeometry.standard_quotients_perfect`), and
  `Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses` (the recorded
  `SheafOfModules.StrictPerfectCoefficientRepresentationOfUniverses` interface).
  The node `det-pe-derived-nakayama-first-reduction` has no recorded declaration
  at the time of this delivery, so there is no module to import for that proof
  dependency. Its statement and the two blueprint detail statements were read;
  its vanishing and isomorphism arguments are included in this theorem's proof
  docstring. It supplies no missing object needed to type the present statement.

Edge cases: n=0 in the Lean indexing is exponent one, not the zero quotient level.
The statement covers the empty scheme and zero complex. It covers identity maps
and arbitrary unbounded complexes; neither boundedness nor constructibility is
assumed in the vanishing or isomorphism clauses. Completeness is essential:
the nonzero rational coefficient E has zero reduction but is not derived complete.
No condition that l be invertible on X was introduced. The rank-one regular
module is the free module even when the ambient sheaf category is trivial.

Searches performed before writing:

- `msearch.py ... leanfinder "For a derived complete complex first derived reduction
  detects zero objects and isomorphisms and quotient coefficients have a two term
  free resolution"`: eight hits concerning K-projectives, projective resolutions,
  ordinary derived functors, and truncations; no match.
- `msearch.py ... loogle "IsDerivedComplete, DerivedCategory, mappingCone"`:
  zero hits, unknown identifier IsDerivedComplete.
- `msearch.py ... grep "derived.?[Nn]akayama|[Ii]sDerivedComplete|derived.?[Rr]eduction"
  Algebra/Homology`: zero Mathlib hits.
- `msearch.py ... leansearch "A derived complete complex vanishes if its first
  derived reduction vanishes, and first reduction detects isomorphisms"`: eight
  hits on localization, quasi-isomorphisms and short-complex homology; no match.
- `rg` for derived Nakayama and first reduction in `lean/Sheaf` found the recorded
  resolution, completion, and their consumers, but no theorem containing all
  clauses of this item. `rg` in the upstream `WeilConjectures` tree for these
  notions and `grep -rn` for this blueprint id found no match.
- `rg` for `reduction_and_derived_nakayama`, derived Nakayama and IsDerivedComplete
  in Mathlib and upstream found no competing declaration; the upstream name
  inventory likewise had no match.

No STATEMENT-DISPUTED issue or node fault was found. The sandbox and library
forms both passed `scompile.py` cleanly, without warnings, in approximately
2.8 and 2.9 seconds respectively. Compilation used only the prescribed wrapper.

## Second reading by Q21

A separate second pass reopened the node, the source unit, the two detail
statements, and the final Lean signature. This was a solo dispatcher worker;
no other agent was started and no independent reviewer is claimed here.
The literal unit statement remains unchanged in the JSON.

The first sentence is not just the resolution lemma's exact sequence: the final
signature explicitly includes the bounded rank-one free complex P, its specified
differential and its actual quasi-isomorphic quotient augmentation. This verifies
both the word "perfect" and the claimed resolution, with degrees -1 and 0.
The cone clause uses the natural comparison of the existing derived reduction
and mapping-cone functors, so it retains its dependence on K. The subsequent
zero-object clause has exactly the two antecedents, derived completeness and
vanishing first reduction. The last clause binds the actual morphism f between
two complete objects and applies that same functor to f; it does not merely
assert that K and L happen to be isomorphic. Positive indexing was checked again:
finiteModule n means the quotient by pi_E^(n+1), and reductionFunctor 1 is the
first reduction. The pointwise equation for d fixes pi_E itself, so the resolution
and cone use the same scalar and its same powers. The ambient coefficient and
scheme universes match the recorded dependencies. No extra mathematical
hypothesis, omitted clause, or changed object was found. The only elaboration
repair during compilation was enabling the dependency's existing
`CategoryTheory.Obj` scope, which supplies the ring-object instance; no
mathematical statement changed.
