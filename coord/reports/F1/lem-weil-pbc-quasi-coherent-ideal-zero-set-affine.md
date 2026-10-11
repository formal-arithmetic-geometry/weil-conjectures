## Worker report

The module `Sheaf.AlgebraicGeometry.QuasiCoherentIdealZeroSetAffine` states
`AlgebraicGeometry.Scheme.quasi_coherent_ideal_zero_set_affine`, with proof `sorry`.
No new definition, dependency module, or statement correction is needed.

Hypotheses and clauses, in order:

- `X : Scheme.{u}` is the arbitrary scheme, without finiteness or separation assumptions.
- `K : X.IdealSheafData` is the quasi-coherent ideal, per the project convention recorded
  in STATE.md, QUASI-COHERENT IDEAL SHEAVES. Its actual submodule sheaf is `K.toModules`
  with inclusion `K.toModulesι`; this is not a general module or a merely coherent ideal.
  The source module constructs it as a kernel. Its `range_toModulesι_app` identifies
  sections on each affine open with `K.ideal U` and its inclusion is a monomorphism.
- The first conjunction states injectivity of that inclusion at every stalk; this
  renders the node's parenthetical identification of K_x as an ideal in O_X,x.
- `U : X.affineOpens` binds an arbitrary affine open, with `A = Γ(X,U.1)` and canonical
  chart `U.2.fromSpec`; `x : U.1` binds precisely a point of that open, and
  `(U.2.primeIdealOf x).asIdeal` is its corresponding prime ideal.
- The second conjunction is the iff: `Function.Surjective` of the stalk inclusion
  means its image ideal is the entire structure-sheaf stalk; `¬ K.ideal U ≤ ...`
  is K(U) not contained in the prime. Surjectivity is invariant under the canonical
  identification of the module stalk of O_X with the local ring, so no extra choice
  of a stalk isomorphism is required.
- The third conjunction identifies the intersection of the proper-stalk set with
  U with the chart image of `{p | K.ideal U ≤ p.asIdeal}`. This is exactly
  V(K) cap U = V(K(U)) under the stated canonical identification, including the
  explicit set of primes in the node.
- The fourth conjunction says that the inline proper-stalk set is `IsClosed` in X.
  It does not silently replace that set by Mathlib's support (defined by zero loci).
- The last conjunction quantifies over every Z and i with `[IsClosedImmersion i]`
  and `i.ker = K`, and identifies `Set.range i` with the same proper-stalk set.
  Existence of such i is already the recorded dependency
  lem-weil-pbc-quasi-coherent-ideal-closed-subscheme (K.subscheme, K.subschemeι,
  ker_subschemeι and the closed-immersion instance); the node mentions it as a known
  fact rather than adding an independent existence conclusion.

Dependency declarations inspected and used:

- Mathlib.AlgebraicGeometry.Scheme: Scheme, Scheme.Hom, Spec, Spec.map.
- Sheaf.AlgebraicGeometry.Coherent: its docstring records quasi-coherence as
  SheafOfModules.IsQuasicoherent, not IsCoherent. Here the more specific ideal encoding
  is the project-approved IdealSheafData of def-sbc-closed-immersion-ideal-sheaf.
- Sheaf.Algebra.Homology.ModuleStalkFunctor: RingedSpace.moduleStalkFunctor, its full
  object and map definition; the inclusion map is a linear map on module stalks.
- Mathlib.AlgebraicGeometry.AffineScheme: IsAffineOpen.fromSpec, range_fromSpec,
  isOpenImmersion_fromSpec, primeIdealOf and fromSpec_primeIdealOf.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: IsClosedImmersion and the
  instance for IdealSheafData.subschemeι.
- Mathlib.AlgebraicGeometry.IdealSheaf.Basic: Scheme.Hom.ker and Hom.ker_apply.
- Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme: subscheme, subschemeι,
  ker_subschemeι, subschemeCover, opensRange_subschemeCover_map,
  subschemeCover_map_subschemeι (full signatures and definitions read).
- WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module: toModules,
  toModulesι, range_toModulesι_app and injective_toModulesι_app.

Edge cases checked mathematically: the empty scheme and empty affine open give
vacuous point clauses and empty sets; the zero ideal has proper stalks at every point,
all primes contain its sections, and its closed subscheme is X; the unit ideal has
surjective stalk inclusions everywhere and empty zero set/subscheme. Neither a
Noetherian nor an integral hypothesis is introduced, and all schemes and section
rings use the same explicit universe u. No auto-bound universes or variables occur.

Searches (performed using msearch.py, recorded in searches.jsonl):

- LeanSearch: “quasi coherent ideal sheaf stalk is whole local ring if and only if
  ideal of sections not contained in corresponding prime”; service returned Internal
  Server Error, recorded unavailable (no conclusion from this unavailable service).
- LeanFinder: “quasi coherent ideal sheaf zero locus defined by proper stalk is
  closed and equals image of closed subscheme”; eight hits, notably IdealSheafData.support,
  isClosed_supportSet, supportSet and zeroLocus_isClosed. Source inspection shows these
  define support via affine zero loci, and supply no statement about module stalk maps.
  The generated search gloss inaccurately calls this “non-zero stalk”; it is not used.
- Loogle: `AlgebraicGeometry.Scheme.IdealSheafData, stalk`; zero hits (unknown identifier
  stalk in the query).
- Mathlib grep: `stalk|supportSet_inter|mem_supportSet_iff_of_mem` in
  AlgebraicGeometry/IdealSheaf; nine hits: affine-local support equalities and the
  unrelated stalkFunctor_toImage_injective. None is the full statement here.
- rg on WeilConjectures for the item id and ideal/stalk patterns: no exact statement;
  the ideal-module bridge exists and is imported rather than duplicated.
- rg on lean/Sheaf for the proposed theorem name and zero/stalk/support patterns:
  no exact statement. IntegralIdealGenericStalk uses the same stalk-inclusion
  surjectivity encoding and explicitly cites this node in its proof.

Source checked: the literature checkout is absent on this machine, so the official
Stacks pages https://stacks.math.columbia.edu/tag/01HM and
https://stacks.math.columbia.edu/tag/01IN were opened and read. They agree with the
node's quotient-stalk support and affine quotient description. The five-step natural
language proof is included in the theorem docstring with its DAG dependencies.
No STATEMENT-DISPUTED issue found.

## Second reading by F1

I reread the node statement and the Lean declaration independently. The objects and
 their Lean renderings are:

- The arbitrary scheme X is `(X : Scheme.{u})`; no separation, finiteness,
  Noetherian, integrality, or characteristic hypothesis is added.
- The quasi-coherent ideal sheaf K is `(K : X.IdealSheafData)`, using the project's
  canonical `K.toModules` and inclusion `K.toModulesι` encoding.
- The stalk-inclusion assertion is the first conjunct,
  `∀ x : X, Function.Injective ((RingedSpace.moduleStalkFunctor
  X.toRingedSpace x).map K.toModulesι).hom`, which supplies the node's
  identification of each stalk ideal with an ideal of the local ring.
- An affine open U, its point x, and its corresponding prime are rendered by
  `(U : X.affineOpens)`, `(x : U.1)`, and `(U.2.primeIdealOf x).asIdeal`; the
  section ring is `Γ(X, U.1)` and the chart is `U.2.fromSpec`.
- The affine criterion is the second conjunct: surjectivity of the stalk map iff
  `¬ K.ideal U ≤ (U.2.primeIdealOf x).asIdeal`, exactly equivalent to the node's
  `K_x = O_{X,x}` iff `K(U)` is not contained in the corresponding prime.
- The affine zero-set equality is the third conjunct, with the proper-stalk set
  intersected with `U.1` equal to
  `U.2.fromSpec '' {p | K.ideal U ≤ p.asIdeal}`.
- Closedness of the proper-stalk set is the fourth conjunct `IsClosed {...}`.
- The closed-subscheme clause is the final universal implication over
  `(Z : Scheme.{u})`, `i : Z ⟶ X`, `[IsClosedImmersion i]`, and `i.ker = K`,
  concluding `Set.range i = {...}`. This preserves the node's quantifier order
  and its “for every such immersion” wording.

Edge cases were checked: empty schemes and empty affine opens make the point
quantifiers and sets vacuous; the zero ideal gives all proper stalks and the
identity closed subscheme; the unit ideal gives no proper stalks and the empty
closed subscheme. The shared universe `u` covers all objects without a hidden
universe restriction, and no n, characteristic, or nonempty-index assumption
occurs.

I repeated the existing-definition searches (LeanSearch, LeanFinder/Loogle, and
grep over Mathlib, `WeilConjectures`, and `lean/Sheaf`). Mathlib's
`IdealSheafData.support` and its affine zero-locus lemmas use a different
zero-locus encoding and do not state the stalk-map criterion; no exact theorem
exists elsewhere. Thus this module remains necessary, with no new definition or
dependency module.

No mismatch was found, so no source, node, statement, or Lean text was changed.
The module compiles with `scompile.py`; its only proof placeholder is the required
theorem `sorry`.
