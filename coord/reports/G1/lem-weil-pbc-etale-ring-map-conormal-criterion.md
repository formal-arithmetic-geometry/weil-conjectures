## Worker report

The module states the conormal criterion, including existence and S-linearity of the
map specified by the derivative formula. Its only theorem proof is `sorry`; no
new definition or dependency module is required. The node is unchanged outside `lean`.

Hypothesis and clause correspondence:

- Commutative rings R and S and the given R→S: `{R : Type u} {S : Type v}`,
  `[CommRing R] [CommRing S] [Algebra R S]`. Both universes are explicit and independent.
- n≥0 and P=R[x₁,…,xₙ]: `(n : ℕ)` and `MvPolynomial (Fin n) R`.
- Surjective R-algebra presentation: `α : MvPolynomial (Fin n) R →ₐ[R] S`,
  `hα : Function.Surjective α`.
- J=ker α and finite generation: `J := RingHom.ker α.toRingHom` and `hfg : ... .FG`.
- J/J²: Mathlib's `Ideal.Cotangent` (Ideal/Cotangent.lean), defined as the quotient
  of J by J•⊤, which is J² inside J. Its quotient map is `Ideal.toCotangent`.
- S=P/J module structure: the existing `RingHom.quotientKerEquivOfSurjective hα`
  identifies P/J with S; `Module.compHom J.Cotangent e.symm.toRingHom` transports
  the existing P/J-module structure to S. This specifies the actual scalar action,
  with no chosen or postponed module data.
- Free module on dx_i: `Fin n → S`, canonically equal to the finite direct sum;
  coordinate i is the coefficient of dx_i.
- Well-defined S-linear map: `∃ d : J.Cotangent →ₗ[S] (Fin n → S)`.
- Formula on every class: `∀ (g : J) (i : Fin n), d (Ideal.toCotangent J g) i =
  α (MvPolynomial.pderiv i g.1)`. The coordinate formula is exactly the displayed
  sum in the node. Surjectivity of `Ideal.toCotangent` makes d unique, so an
  existential with this formula is exactly the specified map, not an arbitrary map.
- Etaleness iff bijective: `Etale R S ↔ Function.Bijective d`.
  The brief's ÉTALE RING MAPS convention expressly permits `Algebra.Etale` here.
  This is etaleness of the given R→S (not of α). The dependency
  def-weil-etale-morphism has Mathlib match `AlgebraicGeometry.Etale`,
  Mathlib.AlgebraicGeometry.Morphisms.Etale; its full definition was inspected.
  The affine comparison identifies this with ring etaleness as allowed by the brief.
  `Algebra.Etale` is imported from Mathlib.RingTheory.Etale.Basic.

Edge cases: n=0 gives the zero free module and the exact zero-variable criterion;
zero rings and S=0 are allowed (no nontriviality binder); J=0 is allowed. No
Noetherian, characteristic, finite type beyond the given finite presentation,
or reducedness assumptions were added. Every variable and universe is bound.
No statement fault or dispute was found.

Searches: msearch.py LeanFinder query 'etale algebra iff conormal map of polynomial
presentation bijective' returned StandardEtalePresentation.lift_bijective,
RingHom.Etale.of_bijective, Algebra.FormallyEtale.iff_comp_bijective and related
ring-map results, none the criterion. Loogle 'Algebra.Etale, Function.Bijective'
returned four unrelated etale-neighborhood existence lemmas. msearch.py grep
'conormal|kerCotangentToTensor' in RingTheory returned the canonical map,
exactness, and injectivity criteria, no full statement. Direct rg of
WeilConjectures for conormal and the item/declaration names found only an unrelated
conormal-sheaf comment; rg of lean/Sheaf found other conormal results and the
colimit proof docstring mentioning this item, not this statement. The upstream
name table had no item hit. Mathlib's Ideal.Cotangent, quotient-kernel equivalence,
Module.compHom, and MvPolynomial.pderiv already supply all needed notions.

Source checked online because this machine has no local Stacks algebra.tex:
[00U1](https://stacks.math.columbia.edu/tag/00U1) gives finite presentation plus
vanishing kernel/cokernel; [00U9](https://stacks.math.columbia.edu/tag/00U9) uses
the isomorphism J/J²→⊕S dx_i for the chosen presentation.
The declaration docstring carries all four proof steps from the node.

Validation: scompile.py compiled the final module cleanly on the server.
The independent second reader will supply the second-reading section and deliver.

## Second reading by G1

Read independently: the sandbox node and module in full; the sole statement
 dependency `def-weil-etale-morphism`, its Mathlib declaration and affine bridge;
Mathlib's conormal quotient, quotient-kernel equivalence, transported module
structure, partial derivative and algebra-etale definitions. No new definition
nodes, dependency modules, or statement correction occur in this delivery.

Source check: the local Stacks checkout is absent. Read the official
[algebra.tex](https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex)
(copy in the sandbox scratchpad), specifically conventions lines 31–41,
presentation and NL(alpha) lines 35179–35204, Lemma 00S1 lines 35274–35291,
and Definition 00U1 and the proof of Lemma 00U9 lines 39237–39292.
The conventions allow the zero ring. These sections assume general commutative
rings with identity; they impose no Noetherian, characteristic, nontriviality,
or field hypothesis. The presentation differential and finite-presentation
condition give precisely this node's criterion. Also read
[02GJ](https://stacks.math.columbia.edu/tag/02GJ), which identifies scheme
etaleness with etaleness of the affine ring maps.

Objects, hypotheses and conclusion clauses, with their Lean counterparts:

1. Arbitrary commutative rings R and S and a given unital ring map R → S:
   `{R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]`.
   An algebra structure over a commutative ring encodes exactly that map;
   `algebraMap R S` is the given map. Verdict: exact, independent universes.
2. Nonnegative integer n and P = R[x_1,...,x_n]: `(n : ℕ)` and
   `MvPolynomial (Fin n) R`. The zero-based labels of `Fin n` merely relabel
   the n variables. Verdict: exact.
3. Surjective R-algebra presentation α : P → S:
   `(α : MvPolynomial (Fin n) R →ₐ[R] S)` and
   `(hα : Function.Surjective α)`. The algebra-hom commutation condition
   ensures that R → P → S is the given R → S. Verdict: exact.
4. J is the kernel, and is a finitely generated ideal:
   `let J := RingHom.ker α.toRingHom` and
   `(hfg : (RingHom.ker α.toRingHom).FG)`. No generators or further
   finiteness assumptions are required. Verdict: exact.
5. The conormal module J/J²: `J.Cotangent`.
   `Ideal.Cotangent` in Mathlib/RingTheory/Ideal/Cotangent.lean defines
   `J ⧸ (J • ⊤ : Submodule P J)`; `map_toCotangent_ker` identifies its
   kernel inside P with J². `Ideal.toCotangent J` is its surjective
   quotient map (`toCotangent_surjective`). Verdict: the same quotient.
6. Its S = P/J scalar action:
   `let e := RingHom.quotientKerEquivOfSurjective hα` and
   `letI : Module S J.Cotangent := Module.compHom J.Cotangent e.symm.toRingHom`.
   Opened Ideal/Quotient/Operations.lean and Algebra/Module/RingHom.lean:
   e sends the class of h to α(h), and e.symm sends α(h) to that class.
   `Module.compHom` acts by e.symm(s) on the existing P/J-module.
   Consequently α(h) acts on the class of g by the class of hg, exactly
   the source's action. Verdict: exact, fully specified data.
7. Free S-module on dx_1,...,dx_n: `(Fin n → S)` with its pointwise
   S-module structure. Since `Fin n` is finite, every vector has finite
   support; its i-th coordinate is the coefficient of dx_i. Verdict:
   canonically the stated finite direct sum, including n = 0.
8. Well-definedness and S-linearity of the specified map:
   `∃ d : J.Cotangent →ₗ[S] (Fin n → S)`. The domain is the quotient,
   and the linear-map type includes additivity and S-linearity.
   Verdict: both clauses present.
9. Formula on every class of every g in J, with formal derivatives over R:
   `∀ (g : J) (i : Fin n), d (Ideal.toCotangent J g) i =
   α (MvPolynomial.pderiv i g.1)`.
   Opened Algebra/MvPolynomial/PDeriv.lean: `pderiv i` is an R-derivation
   with the usual monomial formula. Coordinate equality is precisely the
   node's displayed sum. Quotient-map surjectivity and function
   extensionality ensure this formula determines d uniquely. Thus the
   existential neither weakens the specified map nor adds a choice of
   another differential. Verdict: exact formula and quantifier order.
10. Spec S → Spec R is etale iff d is bijective:
    `(Etale R S ↔ Function.Bijective d)` in namespace `Algebra`.
    Opened `Algebra.Etale` and `FormallyEtale` in RingTheory/Etale/Basic.lean:
    this is finite presentation with zero Kahler differentials and H₁.
    Opened the dependency's `AlgebraicGeometry.Etale` in Morphisms/Etale.lean,
    its `HasRingHomProperty @Etale RingHom.Etale` instance, and
    `RingHom.etale_algebraMap` in RingHom/Etale.lean. These identify this
    algebra property with the dependency's affine scheme property via
    `HasRingHomProperty.Spec_iff`; the brief explicitly permits the ring
    formulation. Etaleness concerns R → S, not α. Verdict: exact iff.

Edge cases: n = 0 is admitted; `Fin 0 → S` is the zero module and the
coordinate formula is vacuous, while S-linearity still requires a map out
of the entire quotient. J = 0 gives the zero conormal module. S = 0 gives
the empty affine scheme and zero modules (J = P, J² = P); R = 0 is also
allowed whenever the given maps exist. No `Nontrivial` instance is used.
All characteristics are allowed. Universes u and v are separately bound;
no equality of their levels or extra algebra structure is assumed. There
is no infinite index set in the node: its only index set is the finite
set of n variables. Verdict: no excluded edge case.

Independent searches (queries differ from the worker's):

- LeanFinder through msearch.py: 'finite polynomial presentation etale
  precisely when Jacobian induces isomorphism on relation ideal modulo
  its square'. Eight hits, including StandardEtalePresentation and
  exists_etale_mvPolynomial for standard smooth presentations; these
  are special presentations or existence results, not this criterion.
- Loogle through msearch.py: 'Ideal.Cotangent, Function.Bijective'.
  Zero hits.
- LeanSearch through msearch.py: 'A finitely presented commutative algebra
  is etale if and only if its relation module maps isomorphically to the
  free module of differentials'. Service unavailable (Internal Server
  Error), recorded without a verdict for that unavailable search kind.
- Direct rg in Mathlib/RingTheory for Jacobian, cotangent/bijective in
  both orders, and etale/criterion in both orders; then conormal,
  kerCotangentToTensor and cotangent/bijective in WeilConjectures and
  lean/Sheaf. Read the relevant results: Mathlib's
  `kerCotangentToTensor_injective_iff`, `iff_split_injection`, and
  `exact_kerCotangentToTensor_mapBaseChange` are pieces of the criterion,
  not a theorem containing all its clauses. The project's conormal
  localization/intersection and diagonal-conormal modules serve other
  notions; EtaleDirectedColimitDescent cites this item only in its proof
  docstring. Upstream Smooth/Local uses the injectivity lemma for a
  different local smoothness statement. No duplicate statement found.
- Exact declaration/item-name rg in dag/lean_names_upstream.json,
  WeilConjectures and lean/Sheaf found no existing declaration.

Mismatches and changes: none. Kept the Lean module and node unchanged;
added only this independent reading to the report. H4/H12/H13 require
no extra node or dependency module: all algebraic notions used already
exist in Mathlib, and the etale dependency is usable through the allowed
affine comparison. No private or hollow definitions occur. The sole
proof is `sorry` for the named theorem. The module and theorem docstrings
name the source and blueprint item, and the theorem docstring carries
all four node proof steps with their essential dependency identifiers.
All three imports are used. The declaration namespace, header, file
location and 100-character line limit meet the conventions.

Validation: scompile.py compiled this 49-line module on the server in
1.5 seconds, with no errors or warnings. Checked by direct string comparison
that lean.statement is verbatim the signature through the conclusion
before `:=`; every variable and universe is explicitly bound. Delivery
preflight and server compilation are run below by deliver2.py.
