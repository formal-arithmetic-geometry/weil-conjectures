## Worker report

The module Sheaf.Paper.LineZeroGeometry states the one theorem
AlgebraicGeometry.PurityVectorBundle.lineZeroGeometry, with proof `sorry`.
There are no definitions, helper axioms, or additional postponed theorems.
The original natural-language statement and its nine proof steps are unchanged.

The earlier BLOCKED message was investigated. The ledger's N9 landing is a stage-1
split, not a stage-2 statement: both the checked-out node and the immutable live
sheaf-dag node have no lean record or reviewed_lean. There is no repair note.
Consequently this delivery supplies the missing Lean statement; it does not
re-submit the unchanged stage-1 split.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| Fixed purity datum and algebraic closure k | `P : WeilConjectures.PurityFiniteSetting.{u}`, using `P.field.k` |
| A separated finite-type k-scheme B | `B : Scheme.{u}`, `b : B ⟶ Spec (CommRingCat.of P.field.k)`, `[IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]` |
| Rank-one bundle with its given total space, projection, module and zero section | `V : PurityVectorBundle P B b 1`, with `V.E`, `V.p`, `V.𝓔`, `V.zeroSection`; `V.phi` is the recorded over-base isomorphism to the actual relative spectrum |
| B and E are locally Noetherian and quasi-compact | `∃ hB : IsNoetherian B, IsNoetherian V.E ∧ ...`; Mathlib's IsNoetherian extends IsLocallyNoetherian and CompactSpace. The existential hB is a conclusion witness, not an added Noetherian hypothesis. |
| E separated and finite type over k | `IsSeparated (V.p ≫ b)`, `LocallyOfFiniteType (V.p ≫ b)`, `QuasiCompact (V.p ≫ b)` |
| Projection separated, finite type, smooth of relative dimension one | `IsSeparated V.p`, `LocallyOfFiniteType V.p`, `QuasiCompact V.p`, `SmoothOfRelativeDimension 1 V.p` |
| Compactification with open immersion j, proper r, rj=pi | `c : Compactification V.p`; its existing fields are `c.i`, `c.g`, `c.isOpenImmersion`, `c.isProper`, `c.comm` |
| Completion is Proj Sym(O_B plus E) | `Q : VectorProjectiveCompletion.Presentation B V.𝓔` and `e : c.Z ≅ Q.algebra.relProj`, with `e.hom ≫ Q.algebra.relProjHom = c.g`. Presentation specifies the symmetric algebra of the section module `Γ(B,U) × E(U)`, its actual grading and restrictions. This is the canonical relative-Proj construction, up to an isomorphism over B, rather than an arbitrary compactification. |
| Standard chart with first generator invertible | `(c.i ≫ e.hom).opensRange = VectorProjectiveCompletion.chartOpen Q`. The witnesses ht and a, the generator equation `a(j(m)) = x(m)/t`, and the scalar equation identify the actual dehomogenization. The affineChart/chartMap equation, transported through `V.phi.inv`, fixes j on every affine base open. No arbitrary map or uncharacterized choice replaces j. |
| Zero section is a closed immersion and pi z=id | `IsClosedImmersion V.zeroSection`, `V.zeroSection ≫ V.p = 𝟙 B` |
| D=z(B) is an effective Cartier divisor | `IsEffectiveCartierCenter V.zeroSection`, the existing closed-subscheme predicate equivalent to invertibility of its kernel ideal |
| D to B is smooth of relative dimension zero | `SmoothOfRelativeDimension 0 (V.zeroSection ≫ V.p)`. The source B identifies with D by the closed immersion. |
| Local Krull-dimension equality at every point of D | `∀ x : B, ringKrullDim (V.E.presheaf.stalk (V.zeroSection x)) = ringKrullDim (B.presheaf.stalk x) + (1 : WithBot ℕ∞)`. Closed immersion identifies these source stalks with the divisor stalks. These are local ring dimensions, not dimensions of fibres. |
| Quasi-compact complement E minus D | `QuasiCompact (Scheme.Opens.ι (X := V.E) V.zeroSection.ker.support.compl)`. For a closed immersion the support of its kernel is its image. |
| Every base change, no flatness/Noetherian assumption | `∀ (B' : Scheme.{u}) (h : B' ⟶ B), IsEffectiveCartierCenter (sectionBaseChange V.p V.zeroSection V.zeroSection_spec.1 (Over.mk h))` |
| On each affine frame the original pair is Spec R[t], V(t) | Quantification over every `U : B.affineOpens` and every `frame : VectorBundleZeroSection.Trivialization B 1 V.𝓔 U.1`. The canonical `trivializationMap` is an isomorphism over U sending `zeroRestricted` to `AffineSpace.zeroSection`. Its source is the canonical total space, identified with V.E by V.phi. AffineSpace on the singleton coordinate type `ULift (Fin 1)` is the existing relative polynomial line; AffineSpace.SpecIso supplies the usual affine polynomial model. |
| Each pulled-back affine pair is Spec R'[t], V(t) | For every `R' : CommRingCat.{u}` and `g : Spec R' ⟶ U.1.toScheme`, the conclusion supplies `e' : pullback V.p (g ≫ U.1.ι) ≅ Spec (CommRingCat.of (Polynomial R'))`, with projection the spectrum of Polynomial.C and section the spectrum of `Polynomial.evalRingHom 0`. These equations identify the scheme-theoretic divisor, not just its point set. Taking the affine inverse of U.isoSpec gives the original affine pair as well. |

The polynomial-chart clause quantifies over all affine schemes mapping to U, hence
includes every affine chart in every B' over U. Scheme, ring, module and frame universes
are explicit; `set_option autoImplicit false` is enabled. There are no let/show binders,
file-local notation, private copies, or extra assumptions on B'.

### Dependency declarations

All eight original statement dependencies were read, including their recorded
signatures and docstrings. The module explicitly imports their recorded modules:

- Sheaf.Paper.PurityFiniteSetting: WeilConjectures.PurityFiniteSetting.
- Sheaf.Paper.PurityVectorBundleZeroSection: AlgebraicGeometry.PurityVectorBundle,
  zeroSection, zeroSection_spec; also its published VectorBundleZeroSection affineChart,
  Trivialization, trivializationMap and zeroRestricted interfaces.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: SmoothOfRelativeDimension.
- WeilConjectures.Compactification.RefinementCategory: Compactification.Refinement and
  its public Compactification structure from Defs.
- WeilConjectures.AlgebraicGeometry.RelativeProj.Basic: Scheme.GradedAlgebraData.relProj,
  relProjHom and relProjι.
- WeilConjectures.AlgebraicGeometry.EffectiveCartier and its separate existing
  WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier module:
  IsEffectiveCartierCenter and isEffectiveCartierCenter_iff_isInvertible_ker.
  EffectiveCartier alone does not publicly import this predicate's owning module;
  the explicit additional public import fixes visibility without redefining it.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and Proper: LocallyOfFiniteType,
  QuasiCompact, IsSeparated and IsProper.

Two already recorded, usable definition nodes are added to stmt_deps because the
signature uses their existing data directly. def-amb-vector-projective-presentation-data
provides VectorProjectiveCompletion.Presentation, t, x, chartOpen and chartMap from
Sheaf.AlgebraicGeometry.VectorProjectiveCompletionData. def-pc-base-change provides
the existing sectionBaseChange construction from the public Picard.Defs dependency
of WeilConjectures.AlgebraicGeometry.BaseChangeConventions. Both are landed definitions;
no new node or dependency-interface repair is needed.

The proof imports include the recorded ProjectiveBundleTautologicalGeometry,
Compactification.ProjectiveSpace, AffineMorphismRelativeSpec, locally-free module and
Noetherian-ring interfaces, together with Mathlib's polynomial symmetric algebra,
Krull-dimension drop, localization, affine-fibre-product and smoothness ingredients.
The docstring records all nine proof steps, including transition functions,
localization denominators, dehomogenization normalization and nonflat base change.

### Edge cases checked

- Empty B: no point or nonempty-frame assertion is introduced; all total schemes and
  projective completions are empty as required.
- Nonreduced and reducible finite-type bases: t remains a nonzerodivisor in R[t].
- Nontrivial line modules: the presentation uses O plus the given module, rather than
  replacing its projective bundle by B times P1. Frames vary on affine opens.
- Arbitrary nonclosed zero-section points: the equality uses local Krull dimensions.
- Zero rings, non-Noetherian rings and nonflat maps R to R': the final clause has no
  nontriviality, flatness, finite-type or Noetherian binder on R'.
- The identity base change and an affine open U itself occur among the quantifiers.

### Searches made

The actual msearch.py records are retained in searches.jsonl.

- leanfinder: "The zero section of a line bundle is universally an effective Cartier
  divisor and the total space has a relative projective compactification". Eight hits,
  all Proj construction/standard-open/properness ingredients, no full statement.
- loogle: `"AlgebraicGeometry", "zeroSection"`. Zero hits.
- grep via msearch.py, Mathlib/AlgebraicGeometry:
  `(zeroSection|zero_section).*(Cartier|[Ss]mooth)`. Zero hits.
- rg of lean/WeilConjectures for lem-pur-line-zero-geometry: no declaration.
- rg of lean/WeilConjectures and lean/Sheaf for Cartier/smooth zero sections found
  general ingredients and the related line_zero_geometry theorem in
  Sheaf.Paper.LineZeroClassEtaleRealization. Its full signature was read: it omits
  the explicit completion, its normalized standard chart, the Noetherian conclusions,
  the quasi-compact complement and the affine-polynomial equations, while asserting
  additional cohomological domain facts. It is not an exact existing match.
- Read VectorProjectiveCompletion.exists_projective_completion and its Presentation
  data. They apply to arbitrary finite rank and give the normalized projective chart,
  but do not state this node's Cartier, local-dimension and arbitrary-base-change
  conjunction. Their existing data are reused, with no duplicate definition.

No STATEMENT-DISPUTED flag or statement correction is needed. No new nodes and no
separate dependency modules are delivered.

### Validation

The full statement compiled cleanly with scompile.py in both sandbox and library
module modes. The final explicit dependency imports are checked again by the
prescribed delivery dry run before push. Independent review belongs to the maintainer.

## Second reading by Q19

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
