## Worker report

The module `Sheaf.AlgebraicGeometry.FiniteMorphismsConstructible` states
`AlgebraicGeometry.Etale.finiteMorphisms_constructible`, with a single `sorry` proof.
It introduces no definitions. The module and theorem docstrings name the blueprint
source and explain all three steps of the node's proof: the finite direct image lemma,
the degree-zero kernel computation, and finite constant zero-module trivializations.
The node's statement and dependencies are unchanged; only its `lean` field is added.

Hypothesis and conclusion correspondence:

- The ambient field is `(k : Type u) [Field k]`; it is not required finite or
  algebraically closed. The schemes are `{X S : Scheme.{u}}`.
- The base is a scheme over k by `[S.Over (Spec (.of k))]`. Finite type is exactly
  `[LocallyOfFiniteType (S ↘ Spec (.of k))]` and
  `[QuasiCompact (S ↘ Spec (.of k))]`. These are the finite-type convention of
  `def-weil-pbc-scheme-conventions`. There is no extra separatedness hypothesis.
- The finite morphism is `(f : X ⟶ S) [IsFinite f]`. The source need not be supplied
  a separate structure morphism or a separate finite-type assumption: composing f
  with the base structure morphism gives these when required in the proof.
- The positive integer N and commutative coefficient ring Lambda are `(N : ℕ)` and
  `(Λ : Type (u + 1)) [CommRing Λ]`. The recorded
  `(hcoeff : IsSmoothBaseChangeCoefficients N Λ S)` states `0 < N`, `Finite Λ`,
  `(N : Λ) = 0`, and `IsUnit (N : Γ(S, ⊤))`. The latter pulls back to X along f;
  thus it expresses the coefficient convention on all schemes in this statement
  without an additional assumption. `hcoeff.2.1` supplies the existing finiteness
  predicate explicitly to the constructibility predicate, with no duplicate instance.
- The sheaf F on the small etale site of X is
  `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. This is the project's
  constant-ring module encoding, rather than an O_X-module or an abelian-only sheaf.
  Constructibility is
  `hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F`, precisely the
  recorded predicate with finite constructible locally closed strata and finite
  constant module trivializations.
- R^q f_*F is written explicitly as
  `((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).obj
    ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))`.
  The sheaf is placed in degree zero; the derived functor is the module-valued
  instance of the recorded direct-image definition. No alternative construction is used.
- The first conjunct quantifies `∀ q : ℕ` and applies the recorded constructibility
  predicate on S to this R^q f_*F. Natural-number q covers exactly every q >= 0,
  including zero, with its displayed cast to the integer homology degree.
- The second conjunct quantifies `∀ q : ℕ, q > 0 → IsZero ...` for the identical
  higher direct image. In an abelian sheaf category `IsZero` expresses vanishing;
  q > 0 is exactly the stated bound q > 2 * 0, without adding a dimension hypothesis
  or a tautological conclusion about the numerical equality 2 * 0 = 0.

Dependency declarations read and used:

- `sbc-def-coefficient-conventions`: public import
  `Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients`, declaration
  `AlgebraicGeometry.Etale.IsSmoothBaseChangeCoefficients`; read its complete
  definition and docstring. Its other vocabulary is reused through its public imports.
- `def-weil-pbc-direct-image`: public import
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, declaration
  `AlgebraicGeometry.Etale.lowerStar`, whose definition is continuous pushforward
  along the small-etale base-change functor. The recorded companion
  `AlgebraicGeometry.Etale.rightDerivedLowerStarPlus` lives in public import
  `WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence`; read its full
  category and Grothendieck hypotheses, source/target and definition.
- `def-weil-pbc-etale-constructible-sheaf`: public import
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`, declaration
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`; read its docstring
  and full finite stratification/trivialization definition.
- `def-weil-pbc-scheme-conventions` has a convention-only record, no module or
  declaration. Its finite and finite-type properties are Mathlib `IsFinite`,
  `LocallyOfFiniteType` and `QuasiCompact`, imported from
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` and `.FiniteType`; read the definitions.
- Proof dependency `lem-fin-finite-morphism`: non-public import
  `Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage`, declaration
  `AlgebraicGeometry.Etale.finite_directImage_constructible_and_higher_vanishing`;
  read its full signature and six-step proof docstring. It states constructibility
  of underived f_*F and positive-degree vanishing, whereas this item explicitly
  states constructibility of every nonnegative higher direct image.
- Proof dependency `lem-weil-pbc-module-direct-image-left-exact`: non-public import
  `Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`, declaration
  `AlgebraicGeometry.Etale.existsUnique_constantModuleDirectImage_leftExact`;
  read its full scalar-map uniqueness, forgetful compatibility, additive,
  product/kernel preservation and initial exact-sequence clauses and docstring.
  The remaining proof dependencies are already public statement imports.

Edge cases checked mathematically before writing:

- q = 0 is included in constructibility but excluded from vanishing. For f = id,
  a nonzero constructible sheaf therefore is not incorrectly asserted to vanish.
- Positive q gives a zero object, which is constructible with the finite zero
  module; no nonzero or nontrivial-coefficient assumption is imposed.
- Empty X or S and zero F are permitted; the empty partition and zero finite
  module cover these cases. There is no nonemptiness or surjectivity binder.
- N = 0 is excluded by the positive coefficient convention; N = 1 and the zero
  coefficient ring are retained. No extra characteristic condition is added.
- The single scheme universe u and coefficient universe u+1 match the recorded
  small-etale sheaf and derived APIs. Neither the base field nor schemes are
  restricted to universe zero, and no independent test-object universe appears.

Searches (2026-10-16):

- `msearch.py leanfinder`, query "A finite scheme morphism has constructible higher
  direct images of constructible etale module sheaves and all positive higher
  direct images vanish": 8 hits. These include `Scheme.Hom.isConstructible_image`,
  `isLocallyConstructible_image`, etale-morphism instances, finite-type predicates,
  and affine-limit section lemmas; their returned types concern subsets, morphisms,
  or sections, not the required module-sheaf statement.
- `msearch.py loogle`, query `AlgebraicGeometry.IsFinite, CategoryTheory.Sheaf`:
  0 hits.
- `msearch.py grep`, query
  `constructible.*(pushforward|directImage)|(pushforward|directImage).*constructible`
  in Mathlib `AlgebraicGeometry`: 0 hits.
- `msearch.py leansearch`, query "Finite morphisms preserve constructible etale
  module sheaves and higher direct images vanish in positive degrees": service
  unavailable, Internal Server Error. The other search kinds above completed.
- `rg` of the upstream `WeilConjectures` sources for finite-morphism and
  constructible/direct-image terms found constructible derived predicates and
  unrelated finite geometry, with no exact statement. An exact item-id search
  in upstream yielded no match.
- `rg` of `lean/Sheaf` found the sibling
  `finite_directImage_constructible_and_higher_vanishing`, whose source and full
  signature were read (comparison above); no exact all-degree statement found.
  More general proper constructibility theorems do not have this item's finite
  hypotheses or its degree-zero vanishing bound. The proposed declaration name
  is absent from upstream and `dag/lean_names_upstream.json`.

No new nodes, dependency repairs, or statement corrections are needed. No statement
is disputed. Validation uses only the authorized `scompile.py` and `deliver2.py`
wrappers; no direct Lean build or Git command is used.

## Second reading by Q20

Independent second-reader audit, 2026-10-16. I opened the sandbox node and Lean file,
compared the statement against its original blueprint markdown in the read-only
`/home/ubuntu/work-bp/sheaf/literature/` copy, and read the cited Stacks TeX there.
The shared checkout omits the ignored literature files; the existing literature copy
contains the exact source paths. The source statement and the DAG statement agree.

The node's objects, hypotheses, and conclusion, matched individually:

1. **Field k.** `(k : Type u) [Field k]` introduces the field over which the base is
   of finite type. PASS: no algebraic closure, separable closure, finiteness, or
   characteristic hypothesis is added.
2. **Schemes and structure morphism.** `{X S : Scheme.{u}}` and
   `[S.Over (Spec (.of k))]` give the two schemes and the specified k-structure on S.
   PASS: X obtains its composite structure over k through f; the node does not
   require a separately supplied structure morphism on X.
3. **Finite type of S over k.** `[LocallyOfFiniteType (S ↘ Spec (.of k))]` together
   with `[QuasiCompact (S ↘ Spec (.of k))]` is precisely finite type in
   `def-weil-pbc-scheme-conventions`. I read Mathlib's class definitions in
   Morphisms/FiniteType.lean and QuasiCompact.lean. PASS: separatedness is absent,
   and no independent Noetherian hypothesis is imposed.
4. **Finite morphism.** `(f : X ⟶ S) [IsFinite f]` is the node's finite f. Mathlib's
   Morphisms/Finite.lean defines this as affine with finite maps on affine opens.
   PASS: it is neither restricted to finite etale maps nor required surjective.
5. **Coefficient convention.** `(N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]` and
   `(hcoeff : IsSmoothBaseChangeCoefficients N Λ S)` render the coefficient node.
   I read that dependency's entire statement and definition: `0 < N ∧ Finite Λ ∧
   (N : Λ) = 0 ∧ IsUnit (N : Γ(S, ⊤))`. PASS: this is exactly positive invertible
   annihilator and finite commutative coefficients. Invertibility on X follows by
   pulling back the global unit along f, so a second hypothesis is unnecessary.
6. **The sheaf F and constructibility on X.**
   `F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)` and
   `hF : @Scheme.IsConstructibleEtaleModuleSheaf X Λ _ hcoeff.2.1 F`.
   PASS: these are module sheaves on the small etale site, with the existing
   constructibility predicate and its explicitly supplied `Finite Λ` witness.
   I read the dependency's full definition: finite locally closed partition,
   constructible parts, pullback along its immersions, and etale trivializations
   by constant finite modules. No O_X-module or abelian-only replacement occurs.
7. **Higher direct image, with F placed in degree zero.** Both conclusion clauses
   use the same expression: `DerivedCategory.Plus.singleFunctor _ 0` places F
   in degree zero, `rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ) f` applies
   the existing module-valued derived pushforward, and
   `DerivedCategory.Plus.homologyFunctor _ (q : ℤ)` takes its q-th cohomology.
   PASS: I opened both upstream declarations recorded by
   `def-weil-pbc-direct-image`: `lowerStar` is precomposition with small-etale
   base change, and `rightDerivedLowerStarPlus` is its bounded-below right derived
   functor. These are the node's functors, not new copies or arbitrary maps.
8. **Every nonnegative degree is constructible on S.** The first conjunct is
   `∀ q : ℕ, @Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1 ...`.
   PASS: natural degrees with their cast to integers cover precisely q >= 0,
   including zero; the output predicate is the same dependency predicate on S.
9. **Every positive degree vanishes.** The second conjunct is
   `∀ q : ℕ, q > 0 → IsZero ...` for that identical higher direct image.
   PASS: `IsZero` in the abelian sheaf category means the zero sheaf. It expresses
   exactly q > 0, equivalently q > 2 * 0, without asserting an extra equality
   about the dimension of empty fibres. The conjunction and quantifier scopes
   match the node.

Source check: Stacks etale-cohomology.tex Tag 03QP,
`proposition-finite-higher-direct-image-zero`, gives positive-degree vanishing
for finite maps. Tag 095R, `lemma-finite-pushforward-constructible`, assumes
finite presentation and Noetherian coefficients. These are not silently omitted:
S finite type over a field is Noetherian, finite f over S is finitely presented,
and finite Lambda is Noetherian; the module in this delivery uses the already
recorded specialized `lem-fin-finite-morphism`. I read that node and its full
Lean signature in FiniteConstructibleDirectImage.lean: identical hypotheses,
constructibility of underived f_*F, and vanishing for positive integer degrees.
It is not an exact existing statement of this node, whose first clause covers
all nonnegative derived degrees. I also read the imported
EtaleConstantModuleDirectImageLeftExact.lean signature and proof docstring: it
supplies the canonical constant-ring scalar map and additive, product/kernel,
and initial-exact-sequence preservation in the constant-ring module encoding.
Its representation is the SheafOfModules encoding; the item's statement itself
uses the recorded ModuleCat-valued direct-image encoding, as required. The
corresponding left exactness is also supplied by the upstream lowerStar API.
No new notion, dependency module, or hidden extra hypothesis is needed here.

The theorem docstring reproduces all three DAG proof steps: finite direct image,
the R^0 initial-kernel computation, and the finite constant zero-module
trivializations. I checked the latter two against derived.tex Tag 05TD,
`lemma-left-exact-higher-derived`, proof of (3), and etale-cohomology.tex Tags
03RW and 095E. The zero-module witness can use the same partition as f_*F.
The only theorem proof is `sorry`; there are no new definitions, instances,
local notation, helper theorems, or hidden data choices. Source/blueprint
references, namespace, public statement imports, ordinary proof imports, and
100-character line limits are correct. Universe u and every variable are bound;
the coefficient universe u+1 matches the recorded constructibility, small-etale,
and Grothendieck coefficient interfaces, with no additional universe equation.
The node's `lean.statement` is the verbatim displayed signature from the file.

Edge cases checked independently: q=0 is constructible but not forced to vanish;
q=1 and all larger q do vanish. The identity of Spec k with a nonzero finite
constant sheaf is therefore admitted. Empty X over nonempty S gives zero direct
images, and empty S admits the empty partition. F=0 and the one-element zero
module work. N=0 is excluded by the source coefficient convention, whereas N=1
and the zero coefficient ring are allowed. No positive rank, nonempty fibre,
or nonempty index set is assumed. All characteristics allowed by invertibility
of N remain covered, and the scheme/field universe is arbitrary.

Independent searches (different wording from the first worker):

- `msearch.py ... leanfinder` queried "Finite scheme maps send finite constructible
  small etale module sheaves to constructible sheaves in every derived degree,
  with higher cohomology zero". Eight hits: Chevalley subset-image lemmas,
  SheafOfModules finite-type/presentation predicates, and an affine-limit section
  lemma. Their returned signatures do not state this etale-module assertion.
- `msearch.py ... loogle` queried
  `AlgebraicGeometry.IsFinite, CategoryTheory.Limits.IsZero`: zero hits.
  An earlier query naming `rightDerivedLowerStarPlus` was rejected as an unknown
  identifier in the Mathlib search index; I did not count it as a negative result.
- `msearch.py ... grep` queried `finite.*[Cc]onstructible|[Cc]onstructible.*finite`:
  thirteen Mathlib hits, concerning constructible subsets, prime spectra,
  Chevalley, and finite unions/intersections. I opened Chevalley's declaration
  in Morphisms/FinitePresentation.lean and confirmed its objects are subsets.
- `msearch.py ... leansearch` queried "Every positive derived pushforward of an
  etale sheaf along a finite scheme morphism is zero and every derived pushforward
  of a constructible sheaf is constructible". Service returned Internal Server
  Error, recorded as unavailable, not a no-match verdict.
- Own `rg` searches on upstream WeilConjectures, Mathlib AlgebraicGeometry,
  shared lean/Sheaf, and dag/lean_names_upstream.json used finite/IsFinite,
  constructible, higherDirectImage, the full proposed name and blueprint id.
  Read upstream SixFunctors/Finite/Exact.lean (exactness only) and
  SixFunctors/Etale/Derived/Finiteness/DirectImage.lean (general derived
  finiteness, with different hypotheses/predicate and no finite positive-degree
  zero clause). Read the closest shared finite-direct-image signature above;
  finite-etale constructibility requires etaleness, and general proper/finite-type
  finiteness statements do not state the present two-clause finite-map result.
  No exact existing declaration or duplicate definition was found.

Mismatches found: none. I retained the Lean file and node record unchanged, and
added this independent reading and its search/edge-case evidence. No statement
correction, new node, or dependency repair is warranted. The initial compile
invocation used the shared checkout as its working directory and could not find
the sandbox file; it was rerun from the sandbox through the prescribed wrapper.
Validation results are recorded below.

Second-reader validation: `scompile.py Q20 fin4-thm-finite-morphisms-constructible
lean/Sheaf/AlgebraicGeometry/FiniteMorphismsConstructible.lean` passed cleanly
(sandbox 34.2 s, library 11.0 s). The required `deliver2.py ... --no-push`
printed `OK (dry run): commit 234c9e44a5 passes the preflight and compiles;
nothing pushed`. The final delivery reruns validation with this report note.
