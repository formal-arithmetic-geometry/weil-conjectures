## Worker report

The module `Sheaf.RingTheory.JacobiZariskiConnectingMapNaturality` states
`Algebra.jacobiZariski_connectingMap_naturality`. Its only proof is `sorry`.
No definitions, new nodes, dependency replacements, or statement corrections are needed.
The server compiled the file cleanly on 2026-10-11 (1.8 seconds).

Hypothesis and clause correspondence:

- Commutative rings R → S → B: `(R : Type u) (S : Type v) (B : Type w)`,
  `[CommRing R] [CommRing S] [CommRing B]`, `[Algebra R S] [Algebra S B]`.
  `[Algebra R B] [IsScalarTower R S B]` specifies the composite map, rather than an
  additional mathematical condition on the tower. All universes are explicitly bound.
- The ideal I and quotient q: `(I : Ideal B)` and `let C := B ⧸ I`.
  Its canonical B-algebra structure has structure map `Ideal.Quotient.mk I`;
  its R- and S-algebra structures are induced through B. No properness, primality,
  finiteness, characteristic, or nontriviality condition is imposed.
- The canonical polynomial presentations and their H1: Mathlib `Generators.self S C`
  and `Generators.self B C`, implicit in `H1Cotangent S C` and `H1Cotangent B C`.
  Their polynomial rings are `MvPolynomial C S` and `MvPolynomial C B`, evaluation
  is `MvPolynomial.aeval id`, and H1 is the kernel of the presentation differential.
  This is the naive complex described by the smooth-ring-map dependency, without
  assuming smoothness.
- (a) iota is `let ι := H1Cotangent.map S B C C`. The canonical presentation morphism
  uses `Generators.defaultHom`, fixes the C-labelled variables and maps coefficients
  through S → B. The induced map is C-linear, since source and target algebra C agree.
- (b) theta is `let θ := P.h1CotangentEquivCotangent`, where
  `P := Extension.ofSurjective (IsScalarTower.toAlgHom R B C)
  Ideal.Quotient.mk_surjective`. Its ring is B with the quotient structure map.
  `P.ker` is `RingHom.ker (Ideal.Quotient.mk I)`, equal to I by
  `Ideal.mk_ker`. Therefore `P.Cotangent` is the conormal module I/I² of the
  statement (Mathlib uses the equivalent quotient `I / I • ⊤`).
  The equivalence is the canonical one supplied by the surjection-H1 dependency.
  The auxiliary R parameter supplies the target conormal differential over R;
  the equivalence only depends on the underlying B → C extension.
- (c) partialS and partialB are `H1Cotangent.δ R S C` and
  `H1Cotangent.δ R B C`. They are already bundled C-linear maps. The recorded
  dependency `Algebra.jacobiZariski_homology_sequence` explicitly identifies this δ
  with the coefficient derivative on every representative:
  `∑ α ∈ g.val.support, (α.prod (fun c n ↦ c ^ n)) ⊗ₜ D R S (MvPolynomial.coeff α g.val)`.
  Thus this selects precisely the maps in clause (c), not arbitrary connecting maps.
  Mathlib `Generators.H1Cotangent.δ_eq_δAux` gives the same identification.
- (d) the comparison map is asserted to exist as
  `c : C ⊗[S] Ω[S⁄R] →ₗ[C] C ⊗[B] Ω[B⁄R]`, with
  `∀ (x : C) (s : S), c (x ⊗ₜ[S] D R S s) =
  x ⊗ₜ[B] D R B (algebraMap S B s)`.
  These tensors generate the source C-module by the universal differential
  generators and tensor balancing. Existence with this formula states its
  well-definedness and uniquely determines c; c is not an unconstrained hypothesis.
  Writing the specified map existentially avoids adding a second definition of
  tensor comparison infrastructure. The conormal map is `δ := P.cotangentComplex`.
  `Extension.cotangentComplex_mk` says exactly `δ (f mod I²) = 1 ⊗ₜ D R B f`.
- All four maps' well-definedness and C-linearity are encoded in their bundled
  linear-map types (for c, existence of such a linear map with the generator formula).
- The conclusion is `δ.comp (θ.toLinearMap.comp ι) = c.comp partialS`.
- The S = B consequence is `δ.comp θ.toLinearMap = partialB`. This equality depends
  only on R → B → C and is valid for every S, so including it in the conjunction
  states exactly the advertised specialization without adding a hypothesis S = B.
  When S = B and the middle map is identity, iota and the uniquely specified c
  are identities, as in the node's last proof step.

Dependency declarations read and used:

- `def-weil-pbc-mv-polynomial-ring`: Mathlib.Algebra.MvPolynomial.Basic,
  `MvPolynomial`, `MvPolynomial.algHom_ext`; Mathlib.Algebra.MvPolynomial.Eval,
  `MvPolynomial.aeval`. These underlie `Generators.self` and presentation maps.
- `def-weil-pbc-smooth-ring-map`: Mathlib.RingTheory.Smooth.Basic, `Algebra.Smooth`
  and its `FormallySmooth` clause were read. The needed H1 notion is
  `Algebra.H1Cotangent` in Mathlib.RingTheory.Extension.Cotangent.Basic, exactly
  as the dependency's mathlib_match specifies; no smoothness hypothesis is used.
- `def-weil-pbc-kahler-differentials`: Mathlib.RingTheory.Kaehler.Basic,
  `KaehlerDifferential`, `KaehlerDifferential.D`, `linearMapEquivDerivation`.
- `lem-weil-pbc-nl-presentation-h1-functoriality`:
  Mathlib.RingTheory.Extension.Cotangent.Basic, `Extension.H1Cotangent.map`,
  `map_eq`, `map_id`, `map_comp`, and the canonical wrapper `Algebra.H1Cotangent.map`.
- `lem-weil-pbc-jacobi-zariski-surjection-h1`:
  Mathlib.RingTheory.Extension.ExtendScalars,
  `Algebra.Extension.h1CotangentEquivCotangent`; its docstring and construction,
  and `h1CotangentEquivCotangent_comp_map`, were read.
- `lem-weil-pbc-jacobi-zariski-homology-sequence`:
  Sheaf.RingTheory.JacobiZariskiHomologySequence,
  `Algebra.jacobiZariski_homology_sequence`, read in full and imported.
  Mathlib.RingTheory.Kaehler.JacobiZariski supplies its canonical
  `Algebra.H1Cotangent.δ` and the coefficient derivative `δAux`.

Edge cases checked before writing: I = 0 (conormal module zero), I = ⊤ (zero
quotient ring and zero modules), B the zero ring, identity S → B, R = S, and
arbitrary characteristic. The formulas and map types remain meaningful in every
case; in the identity case they reduce to the advertised quotient identity.
No finite variable restriction occurs: all elements of C index the polynomial variables.

Searches (real launcher calls, stored in searches.jsonl):

- LeanFinder: `Jacobi Zariski connecting map naturality change middle algebra quotient`.
  Eight hits, including `Generators.H1Cotangent.δ_map`, `δ_comp_equiv`, `δ_eq`,
  `δAux_ofComp`, `δ_eq_δAux`. These concern changes of presentations for a fixed
  tower or give the coefficient formula; none states the middle-ring naturality.
- Loogle: `Algebra.H1Cotangent.δ`. Four hits: δ, the two neighboring exactness
  results, and the quotient special case
  `Extension.cotangentComplex_comp_h1CotangentEquivCotangent` (as recorded in the log).
  The full naturality statement is not among them.
- Launcher grep: `δ_map|map_δ|cotangentComplex_comp_h1`, subdirectory RingTheory.
  Results include the JacobiZariski exactness/presentation naturality lemmas and
  ExtendScalars' quotient special case. Read the relevant full signatures.
- LeanSearch: `Jacobi Zariski connecting map naturality quotient`: unavailable,
  Internal Server Error. No verdict claimed for this failed search.
- Direct rg of WeilConjectures and lean/Sheaf for
  `connecting.*natur|jacobi.*natur|H1Cotangent.δ|lem-weil-pbc-jacobi-zariski-connecting-map-naturality`:
  unrelated cohomology naturality, our homology-sequence dependency, and proof
  docstring citations of this item; no existing full statement.
- Direct rg of dag/lean_names_upstream.json, Mathlib, WeilConjectures, and lean/Sheaf
  for `jacobiZariski_connectingMap_naturality`: no collision.

Source check: literature/stacks-project/*.tex is absent on this machine, so read
https://stacks.math.columbia.edu/tag/00S2 and
https://stacks.math.columbia.edu/tag/07E5 online. The former supplies the sequence
and omits precise maps, and the latter supplies the commutative diagram. The
explicit definitions and five-step computation are those in the node.
No statement dispute or node fault found.

## Second reading by C1

I independently read the item node, all six statement-dependency nodes, the delivered
module, and the dependency declarations listed below. No new definition nodes,
dependency modules, or stage-2 statement corrections are present. No mathematical
mismatch was found; the Lean module and node record are retained verbatim.

Source reading: local `literature/stacks-project/*.tex` is absent. I read the upstream
Stacks `.tex` at https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex
(`lemma-exact-sequence-NL`) and
https://raw.githubusercontent.com/stacks/stacks-project/master/more-algebra.tex
(`section-geometrically-regular`, `proposition-characterization-geometrically-regular`,
through the proof of (3) iff (4)), and the rendered pages
https://stacks.math.columbia.edu/tag/00S2,
https://stacks.math.columbia.edu/tag/07E4, and
https://stacks.math.columbia.edu/tag/07E5.
00S2 assumes only ring maps A -> B -> C and explicitly omits the precise maps.
07E4 assumes a field and a Noetherian local algebra; 07E5 additionally assumes
positive characteristic. Those assumptions belong to the geometric-regularity
application, not the generic connecting-map computation of this node. The node
records its general computation as agent-written, and its five steps use only
commutative rings and the quotient surjection. The Lean makes no false claim
that the full general statement is quoted verbatim from 07E5.

Objects, hypotheses, and conclusion, matched item by item (H3):

1. R, S, B are arbitrary commutative rings with ring maps R -> S -> B.
   Lean: `(R : Type u) (S : Type v) (B : Type w)` and the three `CommRing`
   instances, `[Algebra R S] [Algebra S B]`. `[Algebra R B]` and
   `[IsScalarTower R S B]` specify the composite R-action. Every pair of ring
   maps supplies these structures; this adds no flatness, finiteness,
   Noetherian, nonzero, or field hypothesis. Verdict: exact.
2. I is any ideal, C = B/I, and q is its quotient map; the R- and S-actions
   on C come through B. Lean: `(I : Ideal B)`, `let C := B ⧸ I`, and
   `Extension.ofSurjective (IsScalarTower.toAlgHom R B C)
   Ideal.Quotient.mk_surjective`. Reading `Extension.ofSurjective` confirms
   that `P.Ring = B`, its map is q, and its section is chosen from q's
   surjectivity. `P.ker = RingHom.ker q = I` by `Ideal.mk_ker`.
   Verdict: exact, including improper ideals.
3. The canonical presentations X[C] -> C have variables indexed by all
   elements of C, kernel J, and H1 = ker of the naive differential.
   Lean: `Algebra.H1Cotangent S C` and `Algebra.H1Cotangent B C` abbreviate
   `(Generators.self _ C).toExtension.H1Cotangent`. `Generators.self` has
   `val := id`, section `X`, and polynomial evaluation `MvPolynomial.aeval id`.
   `Extension.H1Cotangent` is `LinearMap.ker P.cotangentComplex`;
   `cotangentComplex_mk` gives `1 ⊗ D` on a kernel representative.
   The free polynomial differential basis identifies this with the node's
   formal-partial-derivative differential. Verdict: same model, not a
   smoothness assumption or a finite-variable presentation.
4. Clause (a): iota is induced by S[C] -> B[C], fixing variables and mapping
   coefficients through S -> B. Lean: `let ι := H1Cotangent.map S B C C`.
   I read `H1Cotangent.map`, `Generators.defaultHom`, and `Generators.self`:
   the default hom sends each variable to X of the same element of C.
   It uses the recorded `Extension.H1Cotangent.map` functoriality; the
   resulting map is C-linear because the final ring map is identity.
   Verdict: exact.
5. Clause (b): theta is the canonical H1(C/B) -> I/I² equivalence.
   Lean: `let θ := P.h1CotangentEquivCotangent`. I read the construction
   in `Extension/ExtendScalars.lean`, its section-induced inverse presentation
   map, and `h1CotangentEquivCotangent_comp_map`. It evaluates each variable
   at the chosen lift in B and passes to the conormal quotient. Independence
   follows from the recorded `Extension.H1Cotangent.map_eq`.
   `Ideal.Cotangent` is `I ⧸ (I • ⊤ : Submodule B I)`, precisely I/I².
   The auxiliary base R does not alter this underlying equivalence.
   Verdict: exact canonical equivalence, not an arbitrary isomorphism.
6. Clause (c): partialS and partialB differentiate polynomial coefficients.
   Lean: `H1Cotangent.δ R S C` and `H1Cotangent.δ R B C`.
   I read the imported `Algebra.jacobiZariski_homology_sequence` signature:
   its representative formula specifies exactly these maps. Independently,
   Mathlib `Generators.H1Cotangent.δAux`, `δAux_monomial`, `δ_eq_δAux`, and
   the wrapper `H1Cotangent.δ` give the same sum, including its sign.
   Verdict: exact; no arbitrary snake-map witness is substituted.
7. Clause (d), comparison c: Lean asserts existence of
   `c : C ⊗[S] Ω[S⁄R] →ₗ[C] C ⊗[B] Ω[B⁄R]` with the formula
   `c (x ⊗ₜ[S] D R S s) = x ⊗ₜ[B] D R B (algebraMap S B s)`.
   This encodes well-definedness and C-linearity. Universal differentials
   generate Ω as an S-module, and tensor balancing shows these tensors
   generate the source as a C-module, so the formula uniquely determines c.
   The existential therefore states the specified map, rather than a weaker
   identity involving an unconstrained witness. Verdict: exact.
8. Clause (d), conormal delta: `let δ := P.cotangentComplex`.
   `Extension.cotangentComplex_mk` gives `δ (f mod I²) = 1 ⊗ D R B f`.
   Its domain is the conormal quotient identified in (5), and its codomain
   is C tensor over B with Ω(B/R). Verdict: exact.
9. All four maps partialS, partialB, c, delta are well defined and C-linear:
   their types are bundled C-linear maps; the existence and formula for c
   assert the only map not already constructed by the dependencies.
   Verdict: no omitted well-definedness or linearity clause.
10. Main identity: `δ.comp (θ.toLinearMap.comp ι) = c.comp partialS`.
    This is equality of the specified C-linear maps on every H1(C/S)
    element, with the same order of composition. Verdict: exact.
11. Specialization S = B with identity middle map:
    `δ.comp θ.toLinearMap = partialB`. This clause involves only R -> B -> C,
    so it is valid without imposing identity on the separately supplied S -> B.
    It is the node's quotient-only consequence, applied to the same R and B.
    In the identity specialization, the presentation map and c are identities.
    Verdict: equivalent to the advertised consequence, no extra conclusion.

Dependency audit (H4): I opened the definitions and signatures in Mathlib
`Algebra/MvPolynomial/Basic.lean` (`MvPolynomial`, `algHom_ext`),
`Algebra/MvPolynomial/Eval.lean` (`aeval`), `RingTheory/Smooth/Basic.lean`
(`FormallySmooth`, `Smooth`), `RingTheory/Kaehler/Basic.lean`
(`KaehlerDifferential`, `linearMapEquivDerivation`),
`RingTheory/Extension/Generators.lean` (`self`, both default homs),
`RingTheory/Extension/Basic.lean` (`ofSurjective`),
`RingTheory/Extension/Cotangent/Basic.lean` (`cotangentComplex`,
`cotangentComplex_mk`, `Extension.H1Cotangent.map`, `map_eq`, `map_id`,
`map_comp`, `Algebra.H1Cotangent`, `Algebra.H1Cotangent.map`),
`RingTheory/Ideal/Cotangent.lean` (`Cotangent`),
`RingTheory/Extension/ExtendScalars.lean` (`h1CotangentEquivCotangent` and
its two comparison signatures), and `RingTheory/Kaehler/JacobiZariski.lean`
(the δ definitions and presentation-naturality signatures).
I also read the full project dependency module
`Sheaf.RingTheory.JacobiZariskiHomologySequence`. The recorded dependencies
provide the exact notions used here; no missing notion, unusable dependency,
or private duplicate requires repair.

Edge cases: I = 0 gives zero conormal module; I = top gives the zero quotient
ring. B may itself be the zero ring. There are no `Nontrivial` hypotheses.
Identity S -> B and R = S are allowed. Arbitrary characteristic is allowed.
The three ring universes are independent, explicitly declared, and no test-ring
quantifier is artificially restricted to a smaller universe. Polynomial variables
are indexed by C with no finite or nonempty restriction on presentations;
zero rings still have their zero element as a canonical variable. Empty schemes,
cohomological n = 0, and a separately quantified empty index family do not occur
in this ring-theoretic node. No edge case of the node is excluded.

Independent searches (launcher results appended to `searches.jsonl`):

- LeanFinder: `conormal differential quotient compatible coefficient derivative
  change base ring`. Eight hits. `Generators.H1Cotangent.δAux_toAlgHom`
  concerns two presentations over the same S and T, not changing S to B;
  other hits are auxiliary cotangent/derivation formulas. No full match.
- Loogle: `Algebra.H1Cotangent.map, Algebra.H1Cotangent.δ`. One hit,
  `Algebra.H1Cotangent.exact_map_δ`, exactness rather than the naturality identity.
- Launcher grep: `H1Cotangent.*natur|natur.*H1Cotangent|cotangentComplex_comp_h1`.
  Found only the quotient special case in ExtendScalars; its full signature
  was read. The special case alone does not replace the full item.
- Direct rg of Mathlib RingTheory, WeilConjectures, and project lean/Sheaf for
  `cotangentComplex_comp|δ_map|map_δ|δ_comp|connectingMap_naturality`, and another
  rg of upstream names, WeilConjectures and lean/Sheaf for the full proposed name,
  coefficient-derivative and conormal-naturality wording: only the known special
  case, fixed-tower presentation naturality, the homology-sequence dependency,
  and unrelated geometric/cohomological material. No existing full statement
  or declaration-name collision.
- LeanSearch: `Naturality of first cotangent homology boundary under homomorphism
  of intermediate coefficient rings and a quotient`. Service returned Internal
  Server Error; recorded as unavailable, with no mathematical verdict.

H5/H6/H8/H9: the module introduces no definitions, so no hollow data or new
notion. Its sole theorem has `by sorry`; nothing was proved. The declaration
and module docstrings carry the source and exact blueprint id, and the theorem
carries all five proof steps with their dependency names. The namespace is
`Algebra`, all lines are at most 100 characters, and every variable and universe
is explicitly bound. The homology-sequence import documents and supplies the
selected connecting-map convention; ExtendScalars supplies theta and its
conormal comparison. The node's `lean.statement` was checked programmatically
against the file from `theorem` to `:=` and is verbatim equal.

Changes: appended this independent second-reading section and recorded new
searches; no Lean or node changes were needed. Server compilation with
`scompile.py C1 lem-weil-pbc-jacobi-zariski-connecting-map-naturality
lean/Sheaf/RingTheory/JacobiZariskiConnectingMapNaturality.lean` from the sandbox
succeeded in 1.7 seconds with no errors or warnings.
