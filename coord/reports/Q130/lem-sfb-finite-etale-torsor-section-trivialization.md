## Worker report

The module `Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleTorsorSectionTrivialization`
states `AlgebraicGeometry.finite_etale_torsor_section_trivialization`, with its proof
left as `sorry`. No definition, helper theorem, dependency repair, new node, or
statement correction is needed. Only the item's `lean` field changes. The live
item has a reviewed stage-1 split from NU but no Lean record and no repair note.
The previous worker's prohibition on another split is irrelevant to this stage-2
statement: this delivery retains that split and all its mathematical content.

Hypotheses and clauses, in statement order:

- Arbitrary schemes U and P: `{U P : Scheme.{u}}`; there is no connectedness,
  Noetherian, reducedness, integrality, or nonempty assumption.
- A finite group: `(G : Type v) [Group G] [Finite G]`. Its universe is independent
  of the schemes. The finite-index coproduct exists by Mathlib's smallness instance;
  no additional smallness or equality of universes is a hypothesis.
- The finite etale structure map: `(π : P ⟶ U) [IsFinite π] [Etale π]`.
- Its left action: `(a : G → (P ⟶ P))`, `haπ` (over the base), `ha1`
  (identity), and `hamul` (left action, with categorical composition reversed).
  These are exactly the corresponding fields of the recorded
  `Scheme.GaloisCoverAction`; that structure also requires a quotient universal
  property, which the present node does not assume. Thus the fields are stated
  explicitly using the recorded interface's signatures, without defining another
  torsor notion or assuming quotient data. Group laws imply the action maps are
  automorphisms.
- Simple transitivity on each geometric fibre: `htorsor`, quantifying over
  algebraically closed fields Ω in the schemes' universe, geometric points x,y,
  and equality of their projections, then asserting `∃! g, x ≫ a g = y`.
  This is verbatim the `GaloisCoverAction.simply_transitive` interface (with names
  substituted). A geometric point over any ordinary point is available in this
  universe from the algebraic closure of its residue field. No transitivity on
  ordinary topological points is substituted. Surjectivity need not be assumed
  separately, because the supplied section already implies it.
- A section: `(s : U ⟶ P) (hs : s ≫ π = 𝟙 U)`.
- Translated section s_g: the actual composite `s ≫ a g`, throughout.
- Its clopen subscheme Q_g: `Q : G → P.Opens`, with
  `∀ g, IsClosed (Q g : Set P)`. The open subschemes are Mathlib's actual
  `(Q g).toScheme`, with inclusion `(Q g).ι`.
- Identification of U with Q_g by s_g: `e : ∀ g, U ≅ (Q g).toScheme` and
  `(e g).hom ≫ (Q g).ι = s ≫ a g`. This also ensures Q_g is precisely the
  image, not just some unspecified clopen containing it.
- The inverse of that identification is the restricted projection:
  `(e g).inv = (Q g).ι ≫ π`.
- Pairwise disjointness and coverage: `Pairwise ... Disjoint (Q g) (Q h)` and
  `(⨆ g : G, Q g) = ⊤`.
- The specified scheme coproduct isomorphism: `θ : (∐ fun _ : G ↦ U) ≅ P` and
  `θ.hom = Sigma.desc (fun g ↦ s ≫ a g)`. The coprojections are `Sigma.ι`.
- It is over U: `θ.hom ≫ π = Sigma.desc (fun _ ↦ 𝟙 U)`; its inverse is over U:
  `θ.inv ≫ Sigma.desc (fun _ ↦ 𝟙 U) = π`.
- The prescribed glued inverse: for every g,
  `(Q g).ι ≫ θ.inv = (Q g).ι ≫ π ≫ Sigma.ι ... g`.
  These restrictions on the asserted open cover uniquely specify exactly the
  gluing in the node. Existence of θ as an Iso already supplies both inverse
  equations as actual equalities of scheme morphisms.
- Translation equivariance: `(s ≫ a g) ≫ a h = s ≫ a (h * g)`.
- Coprojection equivariance:
  `Sigma.ι ... g ≫ θ.hom ≫ a h = Sigma.ι ... (h * g) ≫ θ.hom`.
- Equivariance of the inverse:
  `a h ≫ θ.inv = θ.inv ≫ Sigma.desc (fun g ↦ Sigma.ι ... (h * g))`.
  The explicit endomorphism on the right is precisely the left regular action on
  the coproduct. Its components send summand g to summand h*g.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its `Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `WeilConjectures.AlgebraicGeometry.NormalScheme`:
  `AlgebraicGeometry.Scheme.GaloisCoverAction`, specifically its `smul`, `smul_π`,
  `one_smul`, `mul_smul`, and `simply_transitive` signatures. Publicly imported;
  its extra quotient property is deliberately not added as a hypothesis.
- The coproduct node is a Mathlib leaf, with no Lean record required:
  `Mathlib.AlgebraicGeometry.Limits` supplies
  `instHasColimitsOfShapeDiscreteSchemeOfSmall`, `sigmaOpenCover` and
  `disjoint_opensRange_sigmaι`; `CategoryTheory.Limits.Sigma.desc` and `Sigma.ι`
  state the universal coproduct's actual morphisms.
- Proof-only dependencies are imported privately: `Morphisms.Proper` and
  `Morphisms.QuasiFinite` for the finite-morphism node; `Morphisms.FlatMono`
  (with Etale and Separated already imported transitively) for
  `Etale.of_comp`, `IsOpenImmersion.of_flat_of_mono` and
  `IsClosedImmersion.of_comp`; `ResidueField` for `Scheme.SpecToEquivOfField`;
  `FieldTheory.IsAlgClosed.AlgebraicClosure` for `AlgebraicClosure`; and
  `AlgebraicGeometry.Gluing` for `Scheme.Cover.glueMorphisms`, `hom_ext`, and
  `ι_glueMorphisms`. All named proof dependencies thus have their recorded
  modules or Mathlib-match modules available without introducing a cycle.

Source checks: read Stacks `etale.tex`, proposition-properties-sections (024T),
including all three parts and its proof without Noetherian assumptions;
`morphisms.tex`, lemma-finite-proper (01WN); and `schemes.tex`,
lemma-glue-functors (01JJ), including the morphism compatibility/gluing argument.
The module docstring transcribes all six DAG proof steps, including the uses of
geometric points, construction and uniqueness of the glued inverse, and both
forms of equivariance. The node expressly describes the general scheme argument
as agent-formulated in the ILO IX 2.1(i) context, not as a quotation of that
proposition.

Edge cases checked mathematically before writing:

- Empty U: any P mapping to U is empty. All Q_g can be empty, the copies and
  inverse are the unique morphisms, and the geometric-point condition is vacuous.
  No freeness of the action on Hom from an empty scheme is incorrectly asserted.
- Trivial G: there is one summand and the section identifies all P with U.
- Disconnected and nonreduced U: the trivial torsor is the disjoint union of
  copies of U with its full scheme structure, and satisfies all equations.
  The statement never infers a scheme isomorphism just from point bijectivity.
- Noncommutative G: the left convention `a (g*h) = a h ≫ a g` gives h*g in
  every equivariance conclusion, so no commutativity is assumed.
- Independent universes u and v: the actual module compiled with both universal;
  finiteness supplies smallness of G for the scheme coproduct.

Searches made (2026-10-22):

- `msearch.py` LeanFinder: "A section of a finite etale torsor gives an equivariant
  isomorphism from the coproduct of copies of the base with clopen translated
  sections". Eight hits, including `CompHausLike.LocallyConstant.sigmaIso` and
  `AlgebraicGeometry.sigmaMk`, concern topological decompositions or abstract
  Galois-category results, not this full scheme statement.
- `msearch.py` Loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.Etale`.
  One hit, `AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt`, is a local
  finite-complement result, not the statement.
- `msearch.py` grep in Mathlib AlgebraicGeometry:
  `(torsor|GaloisCover).*(section|trivial)|(section|trivial).*(torsor|GaloisCover)`.
  Zero hits.
- Direct `rg` with that expression over both `lean/WeilConjectures` and
  `lean/Sheaf`, plus the exact item id and proposed declaration name.
  No exact declaration. Read `WeilSheaf/SplitTorsor.lean`, especially
  `ProEtale.isIso_sigmaDesc_torsorSection`: it assumes the stronger split-map
  isomorphism and concludes a base-changed isomorphism without the present
  clopen and equivariance clauses. Also read
  `FundamentalGroup/TorsorUnits.lean`, `Scheme.EtaleTorsor.isIso_sigmaDesc_localSection`:
  it concerns additive commutative group torsors, a specified pullback, and an
  already assumed torsor-map isomorphism. Neither matches this lemma for any
  finite group from geometric-fibre simple transitivity.

No STATEMENT-DISPUTED flag or node fault. No new or repaired dependency nodes.
The example `Sheaf.CategoryTheory.CompactObject` is now a withdrawn empty module;
its node points at the upstream definition. The present module follows the
current module/public-import/exposed-section conventions in brief-stage2.

Validation: `scompile.py Q130 lem-sfb-finite-etale-torsor-section-trivialization`
compiled the delivered module against the live published build with exit code 0
and no compiler warnings or errors (sandbox 7.4 seconds, library module 2.9 seconds).
The initial interrupted compile produced no accessible result and was repeated;
no delivery or other mutation was repeated. The required delivery dry run follows.

## Second reading by Q130

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
