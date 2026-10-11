## Worker report

The module states `AlgebraicGeometry.stein_universally_closed_factor` for a universally closed,
quasi-separated morphism `f : X ⟶ Spec A`. The conjunction renders the four properties of the
first Stein map (`UniversallyClosed`, `QuasiCompact`, `QuasiSeparated`, `Surjective`), integrality
of the second map (`IsIntegralHom`), the pushforward structure-sheaf identity, and the factorization
identity. The recorded Stein map is
`AlgebraicGeometry.Scheme.Hom.steinFactorizationBase` from
`WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.

Dependencies used: `def-pc-scheme` is Mathlib `AlgebraicGeometry.Scheme`; the factorization
notion is `AlgebraicGeometry.Scheme.Hom.steinFactorizationBase` in the module above.

Edge cases checked: arbitrary universe `u`, arbitrary commutative ring (including the zero ring),
and arbitrary scheme `X`; no nonemptiness or finiteness assumptions were added.

Searches: `msearch.py leanfinder` for Stein factorization and universal-closed factorization (no
exact result); `msearch.py loogle` for `UniversallyClosed`, `IsIntegralHom`, and pushforward (only
individual Mathlib properties); grep of Mathlib AlgebraicGeometry for relative Spec/Stein terms
(no bundled theorem); `rg` over WeilConjectures for existing Stein declarations (found only the
recorded `steinFactorizationBase`).

The source also describes compatibility with flat base change; the available Lean APIs do not
provide one bundled proposition for that clause, so the module records the canonical factorization
identity and the structural properties explicitly.

## Earlier second reading (a previous round; superseded)

Read the statement, dependencies, and compiled module; the recorded signature matches the file.


## Second reading by R1

Independent reading of the node, its two statement dependencies, their recorded source
signatures, and Stacks `more-morphisms.tex`, label `lemma-stein-universally-closed`
(Tag 03GY), including the full proof and preceding section introduction. The repository's
literature checkout is absent on this machine; the source text was read in
`/home/ubuntu/c1-stacks-review/more-morphisms.tex`, lines 15087--15152.
The section introduces no Noetherian, properness, finite-type, characteristic, or
nonemptiness assumption. The node is its affine-base specialization. The source additionally
states normalization, but the node deliberately selects the other conclusions: no extra
normalization clause was added. The node itself is correct and was not changed.

Object/hypothesis/conclusion checklist (each verdict: exact):

- Arbitrary commutative ring A: `{A : CommRingCat.{u}}`; no field or Noetherian instance.
- Scheme X and map f to Spec A: `{X : Scheme.{u}} (f : X ⟶ Spec A)`.
  Opened Mathlib `Scheme` and `Scheme.Hom`: respectively a locally ringed space locally
  isomorphic to affine spectra, and a morphism of the underlying locally ringed spaces.
- f universally closed and quasi-separated: `[UniversallyClosed f] [QuasiSeparated f]`.
  No additional compactness, separatedness, finiteness, or properness hypothesis.
- B = H^0(X,O_X): `Γ(X, ⊤)`, the actual structure-sheaf global-section ring.
- q canonical and s induced by f: `X.toSpecΓ` and `f.steinFactorizationBase`.
  Opened `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`, lines 42--60.
  The definition is `Spec.map ((Scheme.ΓSpecIso A).inv ≫ f.appTop)` and the existing
  theorem `Scheme.toSpecΓ_steinFactorizationBase` proves q composed with s equals f.
  The worker's extra factorization-identity conjunct was removed: it already follows
  from this recorded definition and is not an additional conclusion in the node.
- q universally closed, quasi-compact, quasi-separated, surjective: the first four
  conjunction entries, using the corresponding Mathlib morphism predicates.
- s integral: `IsIntegralHom f.steinFactorizationBase` (not finite).
- q_* O_X = O_Spec B: `IsIso X.toSpecΓ.c`. This says the canonical sharp natural
  transformation is invertible on every open, hence gives the structure-sheaf identity.
  Sheaves form a full subcategory of presheaves; invertibility here is equivalent to
  invertibility of the corresponding sheaf morphism. The worker's literal equality
  of sheaf objects was replaced: the source means the canonical identification.
- Relative spectrum of f_* O_X: invertibility of pushforward along s of the sheaf map
  `⟨X.toSpecΓ.c⟩`. Its source is s_* O_Spec B and its target is s_* q_* O_X, canonically
  f_* O_X by the existing composition identity. It respects the O_Spec A-algebra
  structure by composition of sharp maps. Since integral s is affine, this canonical
  algebra identification characterizes precisely Spec_Spec A(f_* O_X), as in the
  landed `AffineMorphismRelativeSpec` and `RelativeSpecBaseChange` modules. Opened both
  modules and checked this characterization against their statements/docstrings.
  This uses the existing affine/quasi-coherent algebra anti-equivalence characterization;
  no private relative-spectrum definition was introduced. The worker omitted this clause.
- Flat-base-change compatibility: the final universal quantifier ranges over arbitrary
  schemes T, B', X' and a flat g:T→Spec A, with `IsPullback b s' s g` and
  `IsPullback x q' q b`. The pasted square is the base change of f. The canonical
  s'_* O_B'→s'_* q'_* O_X' is invertible: B' is the relative spectrum of the new
  pushforward algebra, with its specified canonical map q'. Since s' is a base change
  of integral s, it is affine; the same relative-Spec characterization applies.
  Thus the intermediate relative spectrum and its factor map commute with every flat
  base change, without restricting T to affine schemes. The worker omitted this clause.

Edge cases: the zero ring and empty X are included (then B is the zero ring and Spec B
is empty); surjectivity to the empty target is valid. T, B', X' may also be empty.
There are no index sets, n parameters, characteristic restrictions, domains, or nonempty
instances. Every scheme and ring has the same arbitrary universe u; test schemes are
in that universe, including every scheme occurring in the morphism-category base-change
notion. There are no free variables or independent smaller test universes.

Independent searches:

- `msearch.py ... leanfinder "canonical morphism to spectrum global sections universally
  closed flat base change"`: eight results, including individual Flat/UniversallyClosed
  predicates and `isIntegral_appTop_of_universallyClosed`, no bundled theorem.
- `msearch.py ... loogle "AlgebraicGeometry.Scheme.toSpecΓ"`: twelve results, canonical
  map and its naturality/global-sections formulas, no bundled statement.
- `msearch.py ... leansearch "Stein factorization universally closed morphism relative
  spectrum structure sheaf flat base change"`: service unavailable (HTTP internal error),
  recorded without a negative verdict; LeanFinder, Loogle and direct grep completed.
- `rg` for `stein`, `normalization`, `relativeSpec`, `relative.*Spec`, `toSpecΓ`,
  `flatBaseChange` and flat/global-section terms across Mathlib AlgebraicGeometry,
  WeilConjectures, and repository lean/Sheaf. Read the upstream
  `Scheme.Hom.isFinite_steinFactorizationBase`: assumes properness and a Noetherian
  ring, proves only finiteness, hence is not this theorem. Existing project relative-Spec
  and base-change theorems are tools, not the universally closed Stein bundle. No exact
  existing declaration or duplicate definition found.

Repairs: restored both missing conclusion clauses; replaced sheaf-object equality by
canonical-map invertibility; removed the tautological factorization conjunct; expanded
proof docstring to all five source proof steps and added the standard copyright header.
No new definition nodes, dependency modules, definitions, or proofs were needed. Every
proof remains `sorry`; no hollow data, private copies, file-local notation, or instances.
The node's lean.statement was regenerated verbatim from the repaired signature.

Validation: `scompile.py R1 lem-weil-pbc-stein-universally-closed-factor
lean/Sheaf/AlgebraicGeometry/SteinUniversallyClosedFactor.lean` compiled cleanly in 1.7 s.
