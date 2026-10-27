## Worker report

This is a stage-2 statement delivery for the accepted Q42 stage-1 split.
The live item has no Lean record; the inherited stage-1 unchanged-item refusal
therefore does not apply (coord/brief-stage2.md §0). The retained sandbox held
only dispatcher markers, so the module and node record were written here.
No mathematical statement or proof step is changed.

The module Sheaf.RingTheory.HenselianPointedDevissageChart states
AlgebraicGeometry.exists_henselian_pointed_devissage_chart with one sorry.
Its auxiliary henselianChartLocalization bundles the existing LocalizedModule
at a prime with its canonical Localization.AtPrime action. Its data is the
actual fraction construction; the definition contains no sorry or existence
choice. No new mathematical notion or dependency module is needed.

Sources read: literature/stacks-project/flat.tex,
definition-complete-devissage-algebra (05HX),
definition-complete-devissage-at-x-algebra (05HZ),
remark-same-notion (05I0), lemma-existence-algebra (05I1), and the first proof
paragraph of theorem-flattening-local (05PG). The source's stronger full
pointed-devissage notion also includes transcendence and dimension clauses;
this item's statement asks for the displayed pointing conditions only. The
Lean retains exactly those, together with the recorded complete devissage.

Hypothesis and conclusion correspondence:

- Commutative local rings A and B: `(A B : Type u) [CommRing A]
  [CommRing B] [HenselianLocalRing A] [IsLocalRing B]`.
  HenselianLocalRing includes the local-ring structure of A.
- The local homomorphism A → B is `[Algebra A B]
  [IsLocalHom (algebraMap A B)]`; its distinguished maximal ideal is
  `IsLocalRing.maximalIdeal A` throughout.
- Essential finite type means `[Algebra.EssFiniteType A B]`, the existing
  localization-of-a-finite-type-algebra notion. The already existing Mathlib
  leaf def-weil-pbc-essentially-finite-type-algebra is added to stmt_deps;
  it is not copied or restated.
- P is a finite B-module: `(P : Type v) [AddCommGroup P] [Module B P]
  [Module.Finite B P]`. No finite-presentation assumption is added.
- The output finite-type A-algebra C is `C : CommAlgCat.{u} A` with the
  existential class witness `Algebra.FiniteType A C`.
- The output finite C-module is `N : ModuleCat.{max u v} C` with the
  existential witness `Module.Finite C N`.
- A prime q of C is `q : PrimeSpectrum C`; its contraction to the maximal
  ideal is `q.asIdeal.comap (algebraMap A C) = IsLocalRing.maximalIdeal A`.
- D is exactly `Localization.AtPrime q.asIdeal`, with its canonical
  local-ring and A-algebra structures. The map `f : B →ₐ[A] D` is an
  A-algebra map, with `IsLocalHom f.toRingHom` and
  `f.toRingHom.FaithfullyFlat`. Thus its scalar action is fixed by f.
- The required D-linear isomorphism is `Nonempty
  (henselianChartLocalization q N ≃ₗ[D]
  (ModuleCat.extendScalars f.toRingHom).obj (ModuleCat.of B P))`.
  The left side is literally LocalizedModule q.primeCompl N, not an
  arbitrary localization object. The right side is Mathlib's actual
  `D ⊗[B] P`, canonically the source's `P ⊗[B] D` by tensor symmetry.
  extendScalars binds the B-action on D to f explicitly.
- The complete algebra devissage is an existential
  `d : CompleteAlgebraDevissage A C (IsLocalRing.maximalIdeal A) N`.
  In the dependency's notation d.A i is the item's S_i, d.B i is T_i,
  d.M i is M_i, d.rIndex i is r_i, and d.alpha i is alpha_i. Fin d.n
  indexes 1 through n by shifting indices down by one.
- The finite T_i-algebra S_i condition is d.bToA with d.finiteA.
  The specified maps C → S_1 and T_i → S_(i+1) are d.sToA and
  d.bToAnext. Their surjectivity and finite presentation, smoothness,
  geometric irreducibility and generic residue isomorphisms are the
  fields of the recorded structure; they are not replaced by a private
  chain definition.
- Every A → T_i is flat and finitely presented: the first conjunct
  after d is `∀ i, (algebraMap A (d.B i)).Flat ∧
  Algebra.FinitePresentation A (d.B i)`.
- Every residue-field extension gives a nonzero integral domain: the
  next conjunct quantifies over every `a : PrimeSpectrum A`, field K,
  `Algebra a.asIdeal.ResidueField K`, `Algebra A K`, and the compatible
  `IsScalarTower A a.asIdeal.ResidueField K`; its conclusion is
  `IsDomain (d.B i ⊗[A] K)`. IsDomain includes nontriviality. The two
  algebra structures with their tower specify the field extension and
  its composite A-action; they do not impose an extra mathematical
  condition. Fields live in `Type (max u w)`, never a smaller unrelated
  universe that could make the quantification vacuous.
- The primes q_i and p_i are the existential families qi and pi in the
  appropriate PrimeSpectrum types. The first family of equations says
  qi lies over the maximal ideal. The second says pi lies over qi along
  d.bToA. The next universally quantifies over all primes above qi and
  equates them with pi i, expressing uniqueness rather than existence
  alone.
- The first pointing equation uses every i with i.val = 0 and contracts
  pi i along d.sToA to q. The final equation uses every successive pair
  j.val = i.val + 1 and contracts pi j along d.bToAnext to qi i.
- The final 'in particular' clauses are precisely d.firstIso (N ≃ M_1
  over C), d.cokerIso (the quotient by the range is the next M_i over
  T_i), and d.last_zero (the last quotient is subsingleton, i.e. zero).
- Length zero is permitted: no Nonempty index hypothesis occurs;
  d.zero_case says d.n = 0 implies Subsingleton N. All pointing and
  last-step conditions are universally quantified over Fin d.n, hence
  impose no spurious points in the empty-chain case.

Dependency declarations read and used:

- WeilConjectures.Mathlib.RingTheory.Henselian:
  IsStrictlyHenselianLocalRing and its parent HenselianLocalRing;
  the latter and HenselianRing were read in Mathlib.RingTheory.Henselian.
- Mathlib.RingTheory.Finiteness.Defs: Module.Finite.
- Mathlib.RingTheory.Flat.FaithfullyFlat.Basic: Module.FaithfullyFlat;
  Mathlib.RingTheory.RingHom.FaithfullyFlat: RingHom.FaithfullyFlat.
- Sheaf.TraceFormula.CompleteAlgebraDevissage:
  AlgebraicGeometry.CompleteAlgebraDevissage, including every field.
- Mathlib.RingTheory.RingHom.Flat: RingHom.Flat.
- Mathlib.RingTheory.FinitePresentation: Algebra.FinitePresentation.
- Mathlib.LinearAlgebra.TensorProduct.Defs: TensorProduct;
  Mathlib.Algebra.Category.ModuleCat.ChangeOfRings: ModuleCat.extendScalars
  and ExtendScalars.obj', read to verify its actual tensor product and action.
- Mathlib.Algebra.Module.LocalizedModule.Basic: LocalizedModule and
  LocalizedModule.moduleOfIsLocalization.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField and
  Scheme.Hom.residueFieldMap. For affine primes the statement uses
  Ideal.ResidueField from Mathlib.RingTheory.LocalRing.ResidueField.Ideal,
  literally the residue field of Localization.AtPrime.
- Mathlib.RingTheory.EssentialFiniteness: Algebra.EssFiniteType, the
  mathlib_match of def-weil-pbc-essentially-finite-type-algebra.

All recorded proof-dependency modules that exist are imported privately,
including the pointed scheme definition, henselian root-lifting/retraction,
affine finite-type module dictionary, tilde pullback, and smooth geometric
reducedness. Three proof theorem nodes have no recorded declarations:
lem-sfb-pointed-affine-devissage-etale-existence,
lem-trf-devissage-pointed-restriction, and
lem-trf-pointed-devissage-affine-translation. Their modules cannot yet be
imported; these proofs are not needed to type the present sorry statement.

Edge cases checked before writing: P = 0 permits N = 0 and n = 0;
no marked points or terminal index are then required. A field base uses its
zero maximal ideal, which is prime; finite rings and zero modules cause no
failure of the localization or tensor constructions. A non-finitely-presented
finite P remains allowed. IsLocalRing excludes the zero ring, in agreement
with the source's proper maximal ideals. Nonzero fibre rings are expressed
by IsDomain, not by the weaker reduced or subsingleton predicates. Arbitrary
module universes are retained; the output module universe max u v includes
both finite module models and localization/tensor products. All universe and
term variables are explicitly bound, enforced by `set_option autoImplicit false`.

Searches actually run:

- msearch.py leanfinder, 'A finite module over a local essentially finite
  type algebra over a henselian ring admits a pointed complete devissage
  after a faithfully flat local extension': eight hits (HenselianLocalRing,
  IsAdicComplete.henselianRing, HenselianRing, HenselianLocalRing.TFAE,
  IsHausdorff.of_isLocalRing,
  Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq, and formal
  smoothness results); none constructs a complete pointed chain.
- msearch.py loogle, 'HenselianLocalRing, Algebra.EssFiniteType': zero hits.
- msearch.py grep, 'devissage|dévissage|Devissage', RingTheory: zero hits.
- msearch.py leansearch, 'Complete pointed devissage of a finite module
  over a henselian local base': eight completion/henselian hits, none
  gives the chart.
- rg over lean/Sheaf and lean/WeilConjectures for henselian/devissage/chart
  combinations found the pointed affine scheme definition but no existing
  statement of the present henselian algebraic chart.
- rg for the node id in lean/WeilConjectures found no declaration.
- rg over Mathlib RingTheory found Algebra.EssFiniteType in
  EssentialFiniteness.lean; its signature and localization definition were
  opened, as were the tensor extension and localized-module actions.
- The DAG contains def-weil-pbc-essentially-finite-type-algebra, a
  Mathlib leaf; this is reused by the added stmt_deps entry.

No STATEMENT-DISPUTED flag or statement correction is needed. The full node
proof is rendered in the theorem docstring, with all six steps and their
named inputs. The first server compile exposed an implicit-argument mismatch
for moduleOfIsLocalization; named S, M and T arguments repaired it. The next
scompile.py run passed for both sandbox and library module names, with no
errors or non-sorry warnings. The final delivery dry run recompiles the file.

## Second reading by Q69

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
