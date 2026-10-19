## Worker report

The module `Sheaf.AlgebraicGeometry.ArtinSchreierPrimeCharacterComparison` states
`AlgebraicGeometry.Etale.artinSchreier_prime_character_comparison`. Its sole theorem has
proof `sorry`. All four helper definitions have actual bodies, using existing upstream
constructions. The canonical cover data are reused from the existing declaration module
`Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap`, already present in the live
library. The target cites the existing trace-cover theorem only in `proof_deps`; no
duplicate data module is delivered.
No statement correction or dispute.

Hypothesis and clause correspondence:

- The finite field is `(k : Type u) [Field k] [Fintype k]`; the prime and extension degree
  are `(p r : ℕ) [Fact p.Prime] [CharP k p]`, `hr : 1 ≤ r`, and
  `hcard : Fintype.card k = p ^ r`. `[Algebra (ZMod p) k]` supplies the unique prime-field
  embedding used by `Algebra.trace`.
- The coefficient field is `{L : Type (u + 1)} [Field L] [CharZero L]`, with
  `(ℓ : ℕ) [Fact ℓ.Prime]`, `hℓ : ℓ ≠ p`, `[Algebra (Padic ℓ) L]`, and
  `[IsAlgClosure (Padic ℓ) L]`. Thus L is an algebraic closure of Q_ℓ, exactly the
  coefficient field in the node, in the standard ModuleCat universe for the small site.
  Characteristic zero is its usual field structure and makes the two denominators
  invertible; no invertibility of p in the scheme's ring of sections is imposed.
- The fixed prime-field character is `Ψ : AddChar (ZMod p) L`, with `hΨ : Ψ ≠ 1`.
  The given finite-field character is `ψ : AddChar k L`, with `hψ : ψ ≠ 1`.
  `AddChar` packages an additive-to-multiplicative character, whose values are units;
  its identity character is `1`. This is the existing character notion used upstream.
- `∃ b : kˣ` supplies a nonzero parameter. The first conjunct is exactly
  `∀ c, ψ c = Ψ (Algebra.trace (ZMod p) k ((b : k) * c))`. The next conjunct says every
  unit b' satisfying that same formula equals b, so uniqueness is of the trace parameter
  itself, independently of the subsequent geometric assertions.
- Every separated finite-type k-scheme is quantified by `(X : Scheme.{u})`, its
  `[X.Over (Spec (.of k))]`, and separated, locally-of-finite-type, and quasi-compact
  structure-morphism instances. The global function is `(f : Γ(X, ⊤))`.
- `ArtinSchreierTraceMaps k p r (b : k) X f` is the new definition node’s construction.
  Its underlying schemes/projections are `artinSchreierFunctionCover/Projection` for
  `(p ^ r, f)` and `(p, artinSchreierBaseConstants k X b * f)`. These are actual
  pullbacks of x^n-x, hence the displayed relative-Spec polynomial quotients. The fields
  `σ`, `τ`, `σ_root`, `τ_root` specify exactly the translations y+c and t+d over X.
  `θ_root` specifies the trace polynomial, so none of the maps is an arbitrary choice.
- `artinSchreierComparisonQIdempotent M ψ` and
  `artinSchreierComparisonPIdempotent M Ψ` specialize the existing
  `Etale.isotypicIdempotent` on precisely those covers and translations. Its definition
  is the sum `(1/card G) χ(-g) • lowerStarConstantSheafEndOfOver ...`. Here `card k=q`
  by hcard and `card (ZMod p)=p`; the latter upstream endomorphism acts by pullback of
  sections. Thus these are exactly the two displayed projectors, including their signs.
  The constant coefficient sheaves are the monoidal unit `𝟙_`, as in the dependency API.
- `e : image (prime projector) ≅ image (q projector)` is the displayed isomorphism,
  oriented in reverse to identify its arrow with theta pullback. Its first equation
  says `e.hom ≫ image.ι q = image.ι p ≫ lowerStarConstantSheafMapOfOver ... M.θ M.θ_over`.
  This uniquely characterizes e.hom because `image.ι q` is monic. It uses the canonical
  comparison in the node's proof and does not choose a bare unrelated isomorphism.
- Both `Scheme.IsLocallyConstantSheaf (image ...)` conjuncts place the two objects in
  the full subcategory of lisse L-sheaves. An isomorphism between them in the ambient
  sheaf category is also an isomorphism in that full subcategory; no objects are changed.
- `Nonempty (artinSchreierComparisonSheafOf X ψ f ≅ image (q projector))` is the clause
  identifying the left-hand side with `ℒ_{ψ,f}`. This helper is literally the recorded
  `Etale.artinSchreierSheafOf X ψ f`, with the canonical invertibility instance installed.
  It does not redefine the Artin–Schreier sheaf or use the old prime-degree definition
  superseded by the main-20261015 blueprint update.
- The final clause quantifies every separated finite-type k-scheme X' and k-morphism
  `h : X' ⟶ X`, including identities, with new function `h.appTop f`. It supplies new
  canonical trace maps M' and coordinate-preserving cartesian maps uq, up to the old
  covers (`hq`, `hp`, followed by both root equations). The new isomorphism e' satisfies
  the same theta-pullback characterization as e. Coordinate preservation uniquely fixes
  uq and up, so the cartesian maps give the canonical base-change identifications.
- `artinSchreierComparisonBaseMap π π' h a ha` is pullback of sections on the constant
  pushforwards, followed by the inverse composition isomorphism, with target
  `h_* (π'_* L)`. For a cartesian finite cover it is the adjoint of the finite exchange
  isomorphism with the constant-sheaf identification. The last equation asserts the
  naturality square after adjunction and inclusions in `h_* (π'_q* L)`. Its left side
  transports the prime image to the new prime pushforward, uses the projector retraction
  `factorThruImage`, then `h_*.map e'.hom` and the new q-image inclusion. Its right side
  uses e first and transports the q-image. Because base change intertwines translations,
  the transported prime image is already in the new prime eigensheaf, and that retraction
  is the identity there. Finite exchange and exact pullback identify both sides with
  the usual pullback square. This records actual commutation, rather than only the
  existence of an isomorphism after each pullback. The inclusion characterization makes
  all choices of e and e' agree, so these local clauses form a coherent natural family.

Dependency declarations read and used:

- `def-fd-additive-character`: the recorded
  `Mathlib.NumberTheory.LegendreSymbol.AddCharacter`, `AddChar.FiniteField.primitiveChar`,
  whose construction uses `AddChar` and the trace. Also read the current live source of
  `WeilConjectures.Mathlib.NumberTheory.LegendreSymbol.AddCharacter`, `AddChar.compTrace`,
  through `scompile.py --source` because that source module is absent in the older local
  checkout. A prescribed arbitrary nontrivial Ψ is retained, rather than replaced by the
  particular primitive character chosen by primitiveChar.
- `def-fd-artin-schreier-sheaf`:
  `WeilConjectures.FourierTransform.ArtinSchreier`,
  `AlgebraicGeometry.Etale.artinSchreierSheaf`, `artinSchreierSheafOf` and
  `artinSchreierIdempotent`. Read the full signatures and surrounding docstrings, including
  the q-degree definition and the function-pullback construction.
- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology`, together with `Scheme.Etale` and
  `ofArrows_mem_smallEtaleTopology_iff`. The sheaves used here have precisely this site.
- `lem-a1-artin-schreier-trace-cover-map` remains in `proof_deps` and is imported
  from the live `Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap` module. Its
  existing declaration `AlgebraicGeometry.artinSchreier_trace_cover_map` has the
  finite-etale assertion, torsor fibres, polynomial identities, equivariance, kernel
  fibres and coordinate-preserving arbitrary base change used by the proof. The same
  module supplies the seven cover-data declarations used by the statement.
- Existing canonical constructions: `WeilConjectures.SixFunctors.Finite.Isotypic`,
  `Etale.isotypicIdempotent`; the ConstantSheafEnd/ConstantSheafMap modules,
  `Etale.lowerStarConstantSheafEndOfOver`, `lowerStarConstantSheafMapOfOver`; and
  `Etale.lowerStarComp`. Each helper specializes or composes these, with no independent
  new notion. Their full bodies and docstrings were read.
- Proof imports include `Mathlib.FieldTheory.Finite.Trace` (the recorded trace-pairing
  leaf), `WeilConjectures.SixFunctors.Finite.Stalk` (finite stalk formula),
  `WeilConjectures.SixFunctors.Finite.BaseChange` (finite exchange),
  `WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit` (read current live source
  via `scompile.py --source`), and the upstream ArtinSchreier module (as-cover lemma).
  The theorem docstring carries all six natural-language proof steps and their DAG ids.

Edge cases checked before writing and on rereading:

- r=1: the trace polynomial is by and the comparison is the usual scaling of the
  prime-degree cover. No condition r>1 is present.
- p=2 and extensions with p dividing r: nothing assumes Tr(1) is nonzero and Ψ is never
  replaced by the possibly trivial restriction of ψ to the prime field. For q=4, for
  example, the trace character is nontrivial even though its restriction to F_2 is trivial.
- The empty scheme and empty open charts are allowed. In particular, no `CharP Γ(X,⊤) p`
  instance and no `Nontrivial Γ(X,⊤)` binder is required: either would incorrectly
  exclude the empty scheme. The finite field supplies the coefficients in its zero ring.
- f=0 is allowed (split covers), as are disconnected X. No connectedness, geometric
  nonemptiness, or full-cover-automorphism-group hypothesis is imposed.
- The trivial ψ is excluded exactly as in the node; b=0 is excluded by kˣ. No additional
  exclusion on b, f, p, or r is present. The unique-b clause is independent of the
  comparison-existence clause.
- Arbitrary h, identity h, and morphisms from empty X' are all quantified. No etaleness
  of h is assumed. The coefficient field may be any model of the algebraic closure;
  the standard site/coefficient universe separation is retained.

Searches (all on 2026-10-18):

- msearch LeanFinder, `Artin Schreier finite field character sheaf comparison prime field
  trace`: eight hits, including primitiveChar, trace_to_zmod_nondegenerate, and Gauss-sum
  lemmas; no sheaf-comparison theorem.
- msearch Loogle, `AddChar.compTrace, AddChar.mulShift`: zero hits, unknown identifier
  AddChar.compTrace in the Mathlib search service. The live upstream declaration was
  subsequently inspected separately; it defines trace characters, not this comparison.
- msearch grep, `ArtinSchreier|artinSchreier|compTrace`: zero Mathlib hits.
- msearch LeanSearch, `An Artin Schreier character sheaf for a finite field character is
  isomorphic to the prime field character sheaf with trace parameter`: eight hits,
  including FiniteField.Extension.frob, primitiveChar, trace_to_zmod_nondegenerate,
  IsPrimitive and to_mulShift_inj_of_isPrimitive; no matching sheaf statement.
- Direct rg on upstream FourierTransform and `lean/Sheaf` for
  `artinSchreier.*[Cc]ompar|primeCharacter|compTrace|isotypic`: found the generic projector
  and existing q-degree sheaf and properties, and FourierTraceFunctions trace notation;
  no prime-character sheaf comparison. The generic projector and sheaf are reused.
- Required grep for this item's id under upstream WeilConjectures: no matches.
  Repair inspection found the seven definitions bundled in
  `ArtinSchreierTraceCoverMap`. They are extracted with a simultaneous theorem-module
  repair, as return L requests; no second definition remains in the delivered tree.

Sources inspected: the node and all statement-dependency records; Laumon PDF, (0.2),
(1.1.3), (the project server), using pdftotext; the main-20261015 blueprint Artin–Schreier definition
and the parent unramified-nonexceptional proof. The source's trace parametrization,
Lang-torsor character sheaves and f-pullback agree with this statement. The detailed
trace-polynomial comparison is agent-written in the reviewed DAG proof, as recorded there.

## Existing declarations reused

The return diagnostic identified duplicate declarations in the retained
`Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverData` module. The live source
`Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap` already declares, with the same
signatures and bodies, `artinSchreierFunctionCover`,
`artinSchreierFunctionProjection`, `artinSchreierFunctionRoot`,
`artinSchreierBaseConstants`, `artinSchreierTracePolynomial`,
`artinSchreierFibreMap`, and `ArtinSchreierTraceMaps`. I deleted the retained data
module and its auxiliary node copy, removed the extra statement dependency, and changed
the comparison module to import and use this existing module. This follows the return
instruction to reuse an exact declaration rather than rename or restate it.

Searches confirmed the collision and identity: `rg -n` over the shared and live source
found all seven names in `Sheaf/AlgebraicGeometry/ArtinSchreierTraceCoverMap.lean`;
`scompile.py --source Sheaf.AlgebraicGeometry.ArtinSchreierTraceCoverMap` showed the
full signatures and bodies. The target's remaining statement dependencies are exactly
`def-fd-additive-character`, `def-fd-artin-schreier-sheaf`, and
`def-weil-pbc-etale-site`; the trace-cover theorem remains in `proof_deps`.

## Repair of return L on 953dc65cfa4a

The retained packet duplicated seven declarations from the live
`ArtinSchreierTraceCoverMap` module. I removed the duplicate files and node copies,
restored the comparison import to the existing module, and removed only the extra
statement dependency. The comparison helper bodies and theorem signature are unchanged;
no hypotheses or conclusions are changed.

## Second reading by NX

This is the dispatcher's author self-check; the maintainer performs the independent
review. I reread the final comparison signature against the node clause by clause:
the arbitrary nontrivial Ψ and ψ, unique b in kˣ, field/cardinality/coefficient binders,
all separated finite-type X and f, two image projectors with negative-character weights
and denominators q and p, theta-pullback characterization, both lisse conjuncts,
identification with the existing function Artin–Schreier sheaf, and naturality for every
base morphism, including identity and empty-source morphisms. The adjoint square,
root-preserving cartesian comparisons and new comparison characterization are retained.
The edge cases r=1, p=2, p dividing r, f=0, disconnected and empty schemes still apply.

The existing trace-cover declarations were read in full from the live module and matched
to every use in the comparison: `FunctionCover` is the pullback, `FunctionProjection`
is `pullback.snd`, `FunctionRoot` pulls back `coord`, `BaseConstants` composes the
structure map with ΓSpecIso.inv, `TracePolynomial` is the stated Frobenius sum,
`FibreMap` is `pullback.map`, and `TraceMaps` contains the two translation families,
theta, over-base equations, root equations, and addition laws. No duplicate declaration
remains in this delivery. The theorem's original proof dependency and signature are
unchanged. The target file sets `autoImplicit false`; all universes and binders are
explicit. No statement correction or dispute is introduced.

Validation: `scompile.py` exits 0 for the comparison module against the live trace-cover
module, with no errors or warnings. The prescribed `deliver2.py --no-push` run also
passes preflight and per-file compilation. The shared and upstream trees remain read-only;
all edits are confined to this sandbox.
