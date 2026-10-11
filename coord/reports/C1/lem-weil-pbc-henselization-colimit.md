## Worker report

The module `Sheaf.RingTheory.HenselizationColimit` states the node in two named
sorry-only theorems: `RingTheory.pairHenselization_transition_system` (clause 1)
and `RingTheory.pairHenselization_colimit` (clause 2 and the final henselian case).
It introduces no definition. The node copy changes only `lean`.

Source checked: [Stacks 0A04](https://stacks.math.columbia.edu/tag/0A04) and
[Stacks 0A02](https://stacks.math.columbia.edu/tag/0A02), including the proofs.
The local `literature/stacks-project/more-algebra.tex` is absent on this machine,
so the exact named tags were opened on the Stacks website. The former identifies
both the ring and ideal filtered colimits; the latter constructs henselization
as the colimit of the specified étale algebras and proves its adjunction.

Hypotheses and clause-by-clause translation:

- A nonempty directed set is `{Λ : Type u} [Preorder Λ]
  [IsDirected Λ (· ≤ ·)] [Nonempty Λ]`. A preorder is sufficient; antisymmetry
  is immaterial. The index and ring object universes agree. All universes and
  variables are explicitly bound.
- The directed system of commutative rings is `F : Λ ⥤ CommRingCat.{u}`.
  `F.map f` is the map for an order arrow `f : i ⟶ j`. The identity and
  composition conditions are the functor laws, not extra assumptions.
- The ideals are `J : ∀ i, Ideal (F.obj i)`. The hypothesis that transitions
  preserve ideals is `hJ`, an inequality of `Ideal.map` and the target ideal.
- The fixed stage henselizations in clause 1 are `B i` and `η i`. The
  hypothesis `hB` says each is a colimit of exactly the étale-algebra diagram
  in `RingTheory.pair_henselization`: `ObjectProperty.ι` on the full subcategory
  of `Under (F.obj i)` consisting of maps whose spectra are étale and whose
  quotient map modulo `J i` is bijective. `Nonempty (IsColimit c)` gives the
  construction. The isomorphism `e : c.pt.right ≅ B i` satisfies
  `c.pt.hom ≫ e.hom = η i`, so this allows any chosen representative of the
  henselization with precisely its specified structure map, rather than an
  arbitrary henselian ring. The ideals `I_i^h` are written explicitly as
  `(J i).map (η i).hom`; there is no independent unspecified ideal.
- Clause (1) is the existential family `t` of lifted ring maps. Its first
  conjunct is `η i ≫ t f = F.map f ≫ η j`, the required square. Its second
  conjunct quantifies over EVERY ring map `g` commuting with that square,
  giving `g = t f`; uniqueness is not restricted to ideal-preserving maps.
  Its third conjunct states preservation of the extended ideals. The final
  two conjuncts state the identity and composition laws for `t`.
- For clause (2), `G : Λ ⥤ CommRingCat.{u}` is the henselized system and
  `η : F ⟶ G` its structure maps. `hG` uses exactly the same construction as
  `hB`, with structure map `η.app i`. Naturality is the commutation square
  from clause (1). Conversely the family in clause (1), its system laws and
  its squares give exactly such a functor and natural transformation. Thus
  clause (2) is quantified over the prescribed lifted system without fixing
  a particular implementation of its functor data. Its ideal compatibility
  follows from clause (1), and need not be added as an extra assumption.
- `c : Cocone F` with `hc : IsColimit c` is the original ring colimit `A`;
  its legs `c.ι.app i` are the coprojections `α_i`. `I : Ideal c.pt` and `hI`
  specify precisely the union of their SET images of the stage ideals: the
  existential witness `a` lies in `J i` and maps to `x`. This is not a union
  of arbitrary ideal closures. Using an arbitrary colimit cocone instead
  of `colimit F` preserves every representative of the node's colimit.
- `d : Cocone G` with `hd : IsColimit d` similarly specifies `A_infinity^h`
  with coprojections `d.ι.app i`. The existential ideal `Ih` and its element
  membership equivalence give exactly the union of the set images of the
  extended stage ideals, including that this union is an ideal.
- The existential map `ηInf : c.pt ⟶ d.pt` satisfies the equation with ALL
  coprojections required in the node. The colimit property `hc` makes a map
  satisfying these equations unique, so this is the induced map.
- The comparison clause quantifies over every henselization `A, ζ` of the
  base pair `(c.pt,I)`, again using exactly the dependency's étale colimit
  construction and an isomorphism preserving the structure map. The formula
  `∃! u : d.pt ⟶ A, ηInf ≫ u = ζ` is existence and uniqueness among all
  ring maps under `A`. The following universal clause asserts that this
  unique map is bijective and `Ideal.map u.hom Ih = I.map ζ.hom`.
  Bijectivity of a ring homomorphism means it is a ring isomorphism (and,
  in `CommRingCat`, a categorical isomorphism). The ideal equation is the
  required `u(I_infinity^h) = IA^h`. This is precisely the node's explicit
  comparison-map meaning of “is the henselization”; it does not merely
  assert that the colimit pair is henselian.
- The final clause starts with `HenselianRing c.pt I →`, with no assumption
  of henselianness in the general result. Its family `β i` commutes with the
  structure maps and original coprojections; its uniqueness quantifies over
  all ring maps `b` satisfying that equation. The next inequality gives
  `β_i(I_i^h) ⊆ I`. `G.map f ≫ β j = β i` states compatibility.
  The existential `b : d.pt ⟶ c.pt` with `d.ι.app i ≫ b = β i` is the
  induced map on the colimit, and `Function.Bijective b.hom` and
  `Ideal.map b.hom Ih = I` give the requested isomorphism identifying ideals.

Dependency declarations used:

- `Sheaf.RingTheory.PairHenselization`, `RingTheory.pair_henselization`:
  the EXACT diagram and colimit construction appearing in the theorem's
  signature and docstring are used for the hypotheses `hB` and `hG` and for
  the global henselization. The dependency has no separate named definition
  for its diagram, so its recorded expression is used inline, without making
  a competing private definition or replacing it by a universal property.
- `WeilConjectures.Mathlib.RingTheory.Henselian` (imported by
  `PairHenselization`), the recorded `HenselianRing` from Mathlib:
  the predicate on the original colimit pair in the final implication.
  The strict/local clauses of the terminology node are not needed here.
- `Mathlib.CategoryTheory.Limits.HasLimits`, `CategoryTheory.Limits.Cocone`
  and `CategoryTheory.Limits.IsColimit`: both colimit cocones and the stage
  henselization cocones. Full signatures and source docstrings were read;
  `IsColimit` provides desc, fac and uniq. Arbitrary colimit cocones encode
  the same notion as the chosen `colimit` recorded by the dependency.

Edge cases checked before finalizing:

- The empty index set is excluded by the source's filteredness convention;
  the explicit `Nonempty Λ` is necessary, not an extra hypothesis.
- A singleton directed set recovers henselization of one pair; the first
  theorem forces its lifted identity to be the identity.
- Zero rings and zero ideals are included: no nontriviality or proper-ideal
  assumption is imposed. For the zero ideal the identity ring is already
  the pair henselization. An arbitrary whole-ring ideal is also permitted
  at a stage and in the base construction; its henselization may be zero.
- Transition maps and coprojections need not be injective. All image unions
  use existential elements, and no identification of stages with subrings
  is assumed. Equality of mapped ideals is `Ideal.map`, the usual extension
  notion used in the source. In the bijective comparison cases it is also
  the set image of the ideal.
- No Noetherian, finite-type, local, field, or characteristic assumption was
  introduced. All rings and the index inhabit one common universe, so tests
  and diagrams are not vacuous because of an independent smaller universe.

Searches for existing statements/notions (all made for this item):

- `msearch.py leanfinder`, query `henselization of pairs commutes with filtered
  colimits`: eight hits on finite-presentation descent, local cohomology and
  filtered colimits in RingCat/CommRingCat. None states henselization.
- `msearch.py loogle`, query `HenselianRing, IsColimit`: zero hits, with
  `loogle: unknown identifier 'IsColimit'`. This query was not a successful
  absence check; the grep and LeanFinder searches supplied the useful check.
- `msearch.py grep`, query `henseliz|IsPairHenselization`, subdirectory
  `RingTheory`: zero hits. No Mathlib henselization construction was found.
- `msearch.py leansearch`, query `henselization is the colimit of etale
  algebras inducing an isomorphism modulo an ideal`: service unavailable
  (Internal Server Error), so no inference of absence was made from it.
- `rg -n 'henseliz|IsPairHenselization'` in upstream `WeilConjectures`:
  only prose in `EtaleCohomology/Purity/RealSheaves/Boundary.lean`, no
  declaration. Search of the exact node id in upstream returned no match.
- `rg` in the project's `lean/Sheaf` found the usable `PairHenselization`
  construction and `FilteredColimitHenselianPair`; neither states this node.
  The `HenselizationUniversalProperty` node exists but has no Lean record;
  it is only a proof dependency, not needed to write the statement.
- `rg` in upstream, Mathlib, `dag/lean_names_upstream.json` and the project's
  `lean/Sheaf` found no existing declaration named either
  `pairHenselization_transition_system` or `pairHenselization_colimit`.
- `tools/blueprint_refs.py search henselization` found six blueprint units;
  `ancestor lem-weil-pbc-henselization-colimit` gives
  `thm-weil-pbc-finite-etale-lifting`. No new definition node is needed.

Validation: local single-file compilation passes with no errors or warnings.
Both theorem proofs are exactly `by sorry`. No statements or definitions are
proved, no hollow definition is introduced, and there is no statement dispute
or correction.

## Second reading by C1

I reread the node statement and the complete module side by side.

- The index object is `Λ : Type u` with `[Preorder Λ]`,
  `[IsDirected Λ (· ≤ ·)]`, and `[Nonempty Λ]`; the Lean binders match the
  directed-set convention and do not impose antisymmetry or a smaller universe.
- The directed system of base rings is `F : Λ ⥤ CommRingCat.{u}`.  The ideals
  are `J : ∀ i, Ideal (F.obj i)` and `hJ` is exactly the transition inclusion
  via `Ideal.map`; functorial identity and composition are supplied by `F`.
- The stage henselizations are represented by `G : Λ ⥤ CommRingCat.{u}` and
  `η : F ⟶ G`; `hG` says, for each stage, that `G.obj i` with `η.app i` is a
  colimit of precisely the étale-under-ring diagram whose quotient map modulo
  `(J i).map C.hom.hom` is bijective.  This renders the node's prescribed
  `(A_i^h,I_i^h)` and structure maps, with no arbitrary henselian replacement.
- The separate declaration `pairHenselization_transition_system` renders
  clause (1): for each arrow it existentially supplies `t`, gives the square,
  uniqueness among all ring maps, preservation of the extended ideals, and the
  identity/composition equations.  Its hypotheses use the same `F`, `J`,
  `hJ`, and explicit pair-henselization colimit data.
- In `pairHenselization_colimit`, `c : Cocone F`, `hc`, `I`, and `hI` render
  the base colimit and the exact existential image-union description of `I`.
  `d : Cocone G` and `hd` render the henselized colimit.  The existential `Ih`
  and its membership equivalence render the colimit extended ideal.
- The map `ηInf : c.pt ⟶ d.pt` and its equations with every coprojection render
  the induced map in clause (2).  For every target `A` and map `ζ`, the
  displayed henselization-colimit hypothesis is followed by existence and
  uniqueness of `u`, bijectivity, and `Ideal.map u.hom Ih = I.map ζ.hom`; this
  is exactly the node's explicit meaning of “is the henselization”.
- The final implication is guarded only by `HenselianRing c.pt I`.  Its `β`
  family has the required square, unrestricted uniqueness, ideal inclusion,
  and transition compatibility; the induced `b` has the coprojection
  equations, bijectivity, and the ideal equality.  No conclusion clause is
  omitted or strengthened.

No mismatch was found, so no statement, dependency, or module change was
needed.  In particular, the arbitrary colimit cocones used in Lean are the
node's colimits through `IsColimit`, and the explicit ideal membership
formulas preserve the node's union-of-images convention.

Edge cases checked: `Nonempty Λ` excludes the empty directed system as in the
source; singleton systems are covered.  Zero rings, zero and whole-ring
ideals, and noninjective transition maps are allowed.  No Noetherian,
finite-type, local, field, characteristic, or properness assumption appears.
All ring, diagram, and index universes are the common `u`; no case is lost by
an independent universe.  The `n = 0` issue is irrelevant because the source
has no numerical parameter.

Searches were independently checked with `rg` in the repository's
`lean/Sheaf`, in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, and in
Mathlib, plus the recorded LeanFinder/Loogle/LeanSearch searches.  They find
no existing declaration of this theorem or of a henselization-colimit theorem;
`PairHenselization` is the recorded dependency construction and is used
inline.  The source places (Stacks Tags 0A04 and 0A02) agree with the listed
clauses.  Compilation of the unchanged module succeeds with only its two
`sorry` proofs.
