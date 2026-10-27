## Worker report

The module `Sheaf.AlgebraicGeometry.DiagonalizableQuotientCharacterKernel` states
`AlgebraicGeometry.diagonalizable_quotient_character_kernel`, with one sorry and no proved
lemma. The new definition module constructs the canonical objects and arrows from Mathlib;
it has no sorry, chosen representative, or unspecified map. The item statement is unchanged.

Clause-by-clause rendering:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The finitely generated abelian groups are `(M N : Type u) [AddCommGroup M]
  [AddCommGroup N] [AddGroup.FG M] [AddGroup.FG N]`; their homomorphism is `α : M →+ N`.
- `diagonalizableGroup F M` is exactly `hopfSpec` of `AddMonoidAlgebra F M` with
  Mathlib's canonical additive-group-algebra Hopf instance. The multiplication and all
  three Hopf operations are those in the node, without a reduced/smooth replacement.
- `diagonalizableGroupMap F α` is `hopfSpec.map` of
  `AddMonoidAlgebra.mapDomainBialgHom F α`, hence its coordinate map sends e_m to e_(α m).
- The specified quotient map is `diagonalizableGroupMap F α.ker.subtype`: contravariance
  sends the actual kernel inclusion to restriction D(M) → D(ker α).
- Its coordinate map on global sections is `...left.appTop.hom`; the first conjunct
  states `RingHom.FaithfullyFlat` for this map, the usual affine faithful flatness.
- The second conjunct equates the ideal sheaf of the canonical scheme-theoretic kernel
  inclusion `GrpObj.kerι q` with that of `D(α)`. Mathlib defines the scheme-theoretic image
  of any map g as `g.ker.subscheme`, with embedding `g.ker.subschemeι` in
  `Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`. Thus this is equality of closed
  subschemes in D(M), exactly ker(q) = scheme-theoretic image(D(α)).
- The coequalizer of `yoneda.map fst` and `yoneda.map (diagonalizableGroupAction F α)`
  is the pointwise coset presheaf D(M)(T)/D(α)(D(N)(T)). The third conjunct says the
  represented target is an fppf sheaf. The next conjunct gives its sheafification arrow
  `ηq`, with `coequalizer.π _ _ ≫ ηq = yoneda.map q`. Bijectivity of precomposition
  with ηq for every fppf sheaf `Z` is exactly the sheafification universal property,
  and fixes the canonical quotient identification, not just an unrelated isomorphism.
- `Scheme.fppfTopology.over (Spec (.of F))` is the genuine fppf topology on F-schemes.
  On affine schemes its covers are flat locally finitely presented jointly surjective
  families; the affine basis and finite refinements give precisely the node's
  faithfully flat finitely presented algebra coverings. Yoneda and group operations on
  all F-schemes are equivalent to the affine-algebra functors by Zariski gluing.
- The last conjunct quantifies over every `C : Grp (Over (Spec (.of F)))` and inclusion
  `i` with `IsClosedSubgroupScheme i.hom.hom`. It produces a finitely generated additive
  abelian `P` and a quotient map into the actual `diagonalizableGroup F P`, satisfying
  the recorded `IsFppfGroupQuotient i q`. This states that the represented quotient is
  diagonalizable, using a presentation rather than a chosen quotient object.
- No smoothness, reducedness, nontriviality or characteristic restriction occurs.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, for def-weil-field.
- `IsAlgClosed`, Mathlib.FieldTheory.IsAlgClosed.Basic, for def-weil-algebraic-closure.
- `AlgebraicGeometry.Spec` and `Spec.map`, Mathlib.AlgebraicGeometry.Scheme, for
  def-weil-affine-spectrum, through `hopfSpec`.
- `CategoryTheory.GrpObj`, `Grp`, and `IsMonHom`, Mathlib.CategoryTheory.Monoidal.Grp
  and its monoid-object imports; `GrpObj.ker` and `GrpObj.kerι`,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp. These are the recorded
  group-scheme and scheme-theoretic kernel notions of def-sc-group-scheme.
- `AlgebraicGeometry.IsClosedSubgroupScheme`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, for def-sc-group-scheme-subgroup;
  its structure includes homomorphism, injectivity on every algebra and closed immersion.
- `AlgebraicGeometry.IsFppfGroupQuotient`,
  Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry, for
  lem-sfb-affine-normal-quotient-geometry. Its definition and the full theorem were read.
  The presentation includes kernel, fppf sheafification, local surjectivity and torsor.
- New node def-sfb-diagonalizable-group supplies D(M), D(α) and its coset action,
  using `AlgebraicGeometry.hopfSpec`, `CommHopfAlgCat.ofHom`, and
  `AddMonoidAlgebra.mapDomainBialgHom` directly.

Proof-only imports are Mathlib.RingTheory.Noetherian.Basic (`Submodule.FG.of_le`),
Mathlib.AlgebraicGeometry.Morphisms.Separated (affine source separatedness),
Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion (`IsClosedImmersion`), and
Mathlib.AlgebraicGeometry.Sites.Fpqc (representable fpqc descent). The already stated
normal-quotient theorem is publicly imported because its quotient notion is used.
The other proof dependencies (diagonalizable geometric criteria, algebraic-group
homomorphism factorization, split-torus subgroups, character antiduality) have no Lean
record or mathlib_match on this base; their future modules are not imported. None is
needed as statement data here. Their proof steps are retained in the theorem docstring.

Edge cases checked mathematically before drafting: M = 0, N = 0, α = 0, α injective,
α surjective, C trivial, C all of D(M), and characteristic-p groups such as μ_p.
For α = 0 the image is the identity, q is the identity; for injective α the character
kernel is zero and the cokernel is trivial; for N = 0 the quotient is D(M).
Ideal sheaves and arbitrary test algebras retain nilpotents, so μ_p is included.
Universe u covers the field, groups, schemes and their algebra tests; it is arbitrary
and can be enlarged together. No independent lower test-algebra universe occurs.

Searches made with the prescribed msearch.py (all logged in searches.jsonl):

- LeanFinder: `Diagonalizable group scheme Spec group algebra cokernel character kernel`:
  eight hits on diagonals of spectra and representations, no matching theorem.
- LeanSearch: `diagonalizable group scheme Spec monoid algebra character cokernel`:
  abstract cokernels/representation characters, no matching theorem.
- Loogle: `MonoidAlgebra, AddMonoidAlgebra, GrpObj`: no hit (GrpObj unknown to service).
  `MonoidAlgebra.mapDomainRingHom`: exact reusable algebra maps located.
- Mathlib grep: `diagonalizable|Diagonalizable|groupAlgebra|GroupAlgebra` in
  AlgebraicGeometry: zero hits.
- The new-definition LeanSearch and LeanFinder queries about D(M), its spectrum and
  induced map returned representation diagonals and spectrum diagonals, no construction.
  Whole-Mathlib grep `diagonalizableGroup|diagonalisable|diagonalizable group|
  mapDomainBialgHom|hopfSpec` located the component Hopf API, which is reused.
- rg in lean/Sheaf and lean/WeilConjectures found the finite-only
  IsFiniteDiagonalizableGroupScheme (not applicable to infinite finitely generated M),
  the toric special cases and a finite-kernel use of inline Hopf spectra. None defines
  the general canonical D functor or this cokernel theorem. The proposed full names
  were absent from these trees, Mathlib and dag/lean_names_upstream.json.
- DAG definition-node search for diagonalizable/group-algebra found only finite
  diagonalizability and unrelated chart notions. `tools/blueprint_refs.py search
  diagonalizable` returned zero blueprint nodes. The ancestor tool returns None;
  the new node preserves the item's null ancestor and extends its via chain.

Source read locally: Milne PDF printed pp.231--234 (PDF pp.243--246), including the
Hopf formulas, Proposition 12.3, Remark 12.6 and the full proof of Theorem 12.9.
There is no statement dispute or correction. Every delivered Lean file compiles cleanly
through scompile.py, including the module-name compilation and private sibling overlay.

## New nodes

`def-sfb-diagonalizable-group` records the missing specialized group-algebra spectrum
D_F(M), the functorial Hopf-spectrum map, and its right coset action. Its module is
Sheaf.AlgebraicGeometry.DiagonalizableGroup. Each definition has real construction data:
`hopfSpec.obj`, `hopfSpec.map`, and product projections followed by multiplication.
The group algebra and Hopf operations are Mathlib's, not new definitions. Sources are
Milne §12(b), Proposition 12.3, Remark 12.6, Theorem 12.9(a), and §5(j).
The three search kinds are copied verbatim from the wrapper's logged results into
mathlib_searches. The item cites this node; no dependency record is repaired.

Delivery preflight schema repair: the current gate requires `import_flags: []` on the
new node (the current stage2_delivery.py schema includes it), and extracts abbreviation
signatures starting at `abbrev`. Both records were adjusted to match that current gate.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
