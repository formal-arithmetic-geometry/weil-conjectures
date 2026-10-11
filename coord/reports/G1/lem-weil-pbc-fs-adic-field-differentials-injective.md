## Worker report

The module `Sheaf.RingTheory.AdicFieldDifferentialsInjective` states
`KaehlerDifferential.residueField_mapBaseChange_injective_of_formallySmoothAdic`.
Its single proof is `sorry`; no definitions are introduced or proofs completed.
The node is unchanged outside `lean`.

Hypothesis and conclusion correspondence:

- The field k is `(k : Type u) [Field k]`. The algebra C is `(C : Type v)
  [CommRing C] [Algebra k C]`, with `[IsLocalRing C] [IsNoetherianRing C]`
  exactly supplying localness and Noetherianness. These are independent universes,
  so the statement does not restrict the size of C relative to k.
- The maximal ideal m is `IsLocalRing.maximalIdeal C`; the residue field
  K=C/m is the local abbreviation `let K := IsLocalRing.ResidueField C`.
  Mathlib's residue-field algebra and scalar-tower instances use the quotient map,
  not an arbitrary map into a field. `IsLocalRing` includes `Nontrivial C`.
- Adic formal smoothness is the binder
  `h : Algebra.FormallySmoothAdic k C (IsLocalRing.maximalIdeal C)`.
  This is the dependency's full square-zero lifting property, not discrete
  formal smoothness and not a topology on C chosen independently of m.
- The map in the main conclusion is the local `iota`: first identify
  `K ⊗[k] Ω[k⁄ℤ]` with `K ⊗[C] (C ⊗[k] Ω[k⁄ℤ])` using the inverse of
  `TensorProduct.AlgebraTensorModule.cancelBaseChange k C K K (KaehlerDifferential ℤ k)`,
  then apply `(KaehlerDifferential.mapBaseChange ℤ k C).baseChange K`.
  On generators it sends `x ⊗ d a` to `x ⊗ d (algebraMap k C a)`: the inverse
  cancellation sends `x ⊗ d a` to `x ⊗ (1 ⊗ d a)`, `mapBaseChange` sends
  `1 ⊗ d a` to `d (algebraMap k C a)`, and `baseChange` leaves x fixed.
  The first conjunction clause is `Function.Injective iota`.
  Tensor factors are reversed uniformly from the printed Ω⊗K convention using
  the standard canonical tensor symmetry; neither the objects nor the map change.
  The assembled map is K-linear, not merely an arbitrary function.
- The characteristic-zero parenthesis is the second conjunction clause:
  `∀ [CharZero k], Function.Injective ((mapBaseChange ℤ C K).comp iota)`.
  This is specifically injectivity after composing the same iota with the
  canonical differential map `K ⊗[C] Ω[C⁄ℤ] → Ω[K⁄ℤ]`.
- The positive-characteristic parenthesis is the third clause: for each prime
  `p : ℕ` with `[Fact p.Prime] [CharP k p]`, C receives its induced `CharP C p`
  via `charP_of_injective_algebraMap (algebraMap k C).injective p`.
  `ZMod.algebra k p` and `ZMod.algebra C p` give the canonical prime-field
  algebra structures. Bijectivity of `map ℤ (ZMod p) k k` and
  `map ℤ (ZMod p) C C` identifies each integer-relative differential module
  with its prime-field-relative counterpart. These are respectively k-linear
  and C-linear maps carrying d a to d a by `map_D`; tensoring these canonical
  identifications with K identifies the two tensor modules in the node too.
  No extra hypothesis about C's characteristic or prime-field action is assumed.

Dependency declarations read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; its signature abbreviates `IsNoetherian C C`, precisely
  finite generation of every ideal (`isNoetherianRing_iff_ideal_fg`).
- `def-weil-pbc-formally-smooth-adic`: `Sheaf.RingTheory.FormallySmoothAdic`,
  `Algebra.FormallySmoothAdic`. The whole definition and docstring were read;
  its test rings live in `Type (max u v)` and it requires a lift of every
  square-zero quotient algebra map killing a positive ideal power.
- `def-weil-pbc-kahler-differentials` is a Mathlib leaf with no `lean` record;
  its `mathlib_match` supplies `KaehlerDifferential` in
  `Mathlib.RingTheory.Kaehler.Basic`. The definition, universal derivation `D`,
  and `linearMapEquivDerivation` were read in full. The canonical `map`,
  `map_D`, `mapBaseChange`, and `mapBaseChange_tmul` supply the actual maps.
- Auxiliary existing Mathlib machinery: `IsLocalRing.ResidueField` and its
  quotient algebra/tower instances (`Mathlib.RingTheory.LocalRing.ResidueField.Basic`),
  `LinearMap.baseChange` and `TensorProduct.AlgebraTensorModule.cancelBaseChange`
  (tensor-product tower machinery imported by Kaehler.Basic),
  `ZMod.algebra` (`Mathlib.Algebra.Algebra.ZMod`), and
  `charP_of_injective_algebraMap` (`Mathlib.Algebra.CharP.Algebra`).
  None is a new or privately duplicated notion.

Sources checked: the local Stacks checkout is absent on this machine, so the
actual statements and proofs were read at https://stacks.math.columbia.edu/tag/07EL
and https://stacks.math.columbia.edu/tag/07NQ. The former supplies implication
(2)⇒(5) in positive characteristic; the latter's final paragraph supplies
integer-relative differentials and the zero-characteristic case citing 0322.
The docstring carries all seven DAG proof steps and the named inputs for stage 3.

Edge cases checked before writing: a zero local algebra is excluded by the
node's local-ring condition itself (`IsLocalRing` extends `Nontrivial`), so
field-map injectivity is valid even when C has zero divisors. C need not be
complete or finite type; neither restriction is present in Lean. When C is
itself a field, m=0 and the residue field is its quotient by zero, so the
same tensor-cancellation and differential maps apply. Fields of characteristic
zero and every prime characteristic are covered. For a prime field the
source differential module is zero, making the injectivity claim consistent.
Nonperfect and infinitely generated fields are permitted; no finiteness,
separability, or perfection assumption was introduced. No disputed statement
or correction was necessary.

Searches for an existing statement (all via msearch.py unless specified):

- `leansearch`: `formally smooth adic local field algebra injectivity Kahler
  differential residue field`: unavailable, Internal Server Error.
- `leanfinder`: `adic formally smooth local algebra over a field gives injective
  base field Kahler differentials at residue field`: eight hits, notably
  `Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField`,
  `iff_injective_lTensor_residueField`, `iff_injective_cotangentComplexBaseChange`,
  and `iff_split_injection`. These concern discrete formal smoothness and
  presentation cotangent maps, not this adic base-field differential statement.
- `loogle`: `KaehlerDifferential.mapBaseChange, Function.Injective`: zero hits.
- `grep`: `FormallySmooth|injective.*mapBaseChange|mapBaseChange.*injective`
  in `RingTheory/Kaehler`: zero hits.
- Direct `rg` over source `WeilConjectures` for the item id: no hit.
  `FormallySmoothAdic|differentials.*injective|injective.*differentials`
  over source and `lean/Sheaf`: only the existing adic definition and its
  power-series use, no matching theorem. `mapBaseChange` in source RingTheory
  and project RingTheory: no preexisting matching statement. The proposed
  full theorem name has no hit in Mathlib, source, or landed project Lean.
- Direct inspection/grep of `Mathlib/RingTheory/Kaehler/Basic.lean` and
  `Mathlib/LinearAlgebra/TensorProduct/Tower.lean` located the canonical maps,
  base change and cancellation equivalence used above.

Validation: server single-file compilation and the delivery dry run are run
with scompile.py and deliver2.py; the second reader supplies the independent
reading section before delivery. No second reading is claimed here.


## Second reading by G1

I independently read the item node, all three statement-dependency nodes and
their recorded declarations, the delivered module, and Mathlib's actual maps.
The list of objects, hypotheses and conclusions, matched item by item, is:

1. A field k: `(k : Type u) [Field k]`. Exact; no perfection, separability,
   finite generation or characteristic restriction.
2. A commutative k-algebra C: `(C : Type v) [CommRing C] [Algebra k C]`.
   Exact, including an arbitrary specified k-algebra structure.
3. C is local and Noetherian: `[IsLocalRing C] [IsNoetherianRing C]`.
   Exact. I opened LocalRing/Defs: IsLocalRing extends Nontrivial. I opened
   Noetherian/Defs: IsNoetherianRing abbreviates IsNoetherian C C, equivalent
   to finite generation of every ideal, as the dependency node states.
4. Its maximal ideal m and residue field K=C/m:
   `IsLocalRing.maximalIdeal C` and `let K := IsLocalRing.ResidueField C`.
   Exact. ResidueField/Defs defines precisely that quotient, with its field
   instance. ResidueField/Basic supplies quotient-induced C- and k-algebras
   and their scalar tower; no independent choice of residue map is assumed.
5. Formal smoothness for the m-adic topology:
   `h : Algebra.FormallySmoothAdic k C (IsLocalRing.maximalIdeal C)`.
   Exact. I opened the dependency's complete definition: every square-zero
   ideal J in a commutative k-algebra D and every algebra map C -> D/J
   killing a positive power of m admit an algebra-map lift. Test algebras
   have universe max u v, not a smaller independent universe. No discrete
   formal smoothness or completeness is substituted.
6. The universal differential modules: `KaehlerDifferential ℤ k` and
   `KaehlerDifferential ℤ C`. Exact. The dependency is the Mathlib leaf
   Kaehler.Basic, whose definition, D and linearMapEquivDerivation I opened:
   its module represents derivations with exactly the stated universal property.
7. The canonical K-linear map from the base-field differential tensor module
   to the algebra differential tensor module: `iota` is the composition of
   inverse `cancelBaseChange k C K K (KaehlerDifferential ℤ k)` with
   `(mapBaseChange ℤ k C).baseChange K`. Exact. I read cancelBaseChange and
   cancelBaseChange_symm_tmul in TensorProduct/Tower, and map, map_D,
   mapBaseChange and mapBaseChange_tmul in Kaehler/Basic. They give
   `x ⊗ d a -> x ⊗ (1 ⊗ d a) -> x ⊗ d(algebraMap k C a)`.
   Both maps are K-linear. Tensor symmetry converts these K-first tensors
   to the printed differentials-first convention without changing the map.
8. Injectivity of that map: first clause `Function.Injective iota`. Exact.
9. Characteristic-zero parenthesis: second clause
   `∀ [CharZero k], Function.Injective ((mapBaseChange ℤ C K).comp iota)`.
   Exact. Its final map sends x ⊗ d c to x d(residue C c), so it is the
   composition to the actual residue-field differential module, not a new map.
10. Positive-characteristic identification: third clause quantifies over
    `(p : ℕ) [Fact p.Prime] [CharP k p]` and asserts bijectivity of
    `map ℤ (ZMod p) k k` and `map ℤ (ZMod p) C C`. Exact canonical
    identifications. I read ZMod.algebra and charP_of_injective_algebraMap:
    the local CharP C p is derived from the given field algebra structure,
    and the prime-field algebras are canonical. These maps are respectively
    k- and C-linear, and map_D sends d a to d a. Their bijectivity is
    therefore a linear isomorphism, whose tensor extension with K is exactly
    the node's identification of the tensor modules. Compatibility with the
    induced differential map follows on these generating tensors; there is
    no arbitrary existential isomorphism or extra algebra assumption.

Source reading: no Stacks checkout is present in the read-only repository.
I obtained the actual more-algebra.tex in this item's scratchpad from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex.
I read theorem-regular-fs (lines 9872-9910), including its field and
Noetherian-local hypotheses and implication (2) -> (5), and
proposition-fs-flat-fibre-fs, final paragraph (lines 10218-10244).
I also read the online tags https://stacks.math.columbia.edu/tag/07EL,
https://stacks.math.columbia.edu/tag/07NQ and
https://stacks.math.columbia.edu/tag/0322. The hypotheses local to the
07NQ ambient lifting construction are not additional hypotheses on this
standalone differential lemma. The node correctly isolates its input.
Definitions 07EB and 07NI in the tex were checked against FormallySmoothAdic.

Edge cases: zero C is excluded by the source's proper local maximal ideal
and by IsLocalRing's Nontrivial field; no excluded legitimate zero-ring case.
For C a field m=0, the quotient and cancellation maps still give the same
claim. Zero differential modules (e.g. k a prime field) cause no problem.
Every prime characteristic is covered; p=0 is covered by CharZero and p=1
is impossible for a field. Imperfect and infinitely generated fields remain
allowed. Independent u and v cover all sizes of k and C; every variable and
universe in the signature is explicitly bound. There is no index set,
scheme or numerical n in this node, so empty-index, empty-scheme and n=0
cases do not impose further conditions.

Independent searches (different wording from the worker's searches):
- LeanFinder via msearch: "Injective absolute Kähler differential map on the
  closed fibre of a formally smooth local ring" returned eight hits.
  I opened Smooth/Local and read iff_injective_lTensor_residueField,
  iff_injective_cotangentComplexBaseChange_residueField and its general
  version. They are discrete formal smoothness criteria for a presentation
  cotangent map with finite-free differentials, not this adic absolute map.
- Loogle via msearch: "KaehlerDifferential.map, Function.Bijective" returned
  no hits.
- Grep via msearch: "cotangent.*injective|injective.*cotangent" returned
  presentation/Jacobi-Zariski results, not the requested statement.
- LeanSearch via msearch: "absolute differentials of adic smooth local
  algebra inject into closed fiber differentials" was unavailable (Internal
  Server Error); no negative verdict is inferred from this failure.
- Direct rg on WeilConjectures and lean/Sheaf for 07EL, 07NQ,
  residue.*differential, differential.*residue, FormallySmoothAdic and the
  proposed full declaration found adic definitions and different lifting
  lemmas, no matching theorem. The full name is absent from the upstream
  names JSON. Grep of Kaehler/Basic for injective/bijective found no match.

No mismatch found; no Lean or node change was needed. I retained what was
right and added this independent report only. There are no new definition
nodes or dependency modules to review. No statement correction was made.
The sole theorem is left sorry, with no new definitions or completed proofs.
Its module and theorem docstrings cite the source and this blueprint node;
the theorem docstring follows all seven proof steps and names their inputs.
Imports are used, namespace and header follow the project conventions,
lines are at most 100 characters, and the node lean.statement was checked
verbatim against the file signature. Server single-file compilation passed
in 1.5 seconds with no errors or warnings.
