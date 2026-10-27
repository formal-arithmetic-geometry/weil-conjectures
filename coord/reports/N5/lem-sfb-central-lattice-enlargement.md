## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.CentralLatticeEnlargement` states
`AlgebraicGeometry.exists_central_isogeny_of_lattice_enlargement` with its sole proof
`sorry`. There are no new definitions, helper theorems, extra nodes or dependency
repairs. The node is unchanged except for `lean`.

Hypotheses, clause by clause:

- The algebraically closed field is `{F : Type u} [Field F] [IsAlgClosed F]`.
- The F-group schemes are `Grp (Over (Spec (.of F)))`. `hH` uses the existing
  `IsSemisimpleGroupScheme H.X`: smooth, connected, affine, locally finite type
  and quasi-compact, with every smooth connected solvable normal closed subgroup
  terminal. Its existing derived-series definition retains scheme structure.
- The fixed maximal torus is `iT : T ⟶ H` with `hT : IsMaximalTorus iT`.
  `hsplit` identifies T with some `MultiplicativeType.splitTorus F r`.
- X is the actual `Additive (T ⟶ Grp.mk (StandardGroupSchemes.multiplicative F))`;
  X_* is the reverse additive Hom group. Their commutativity instances and
  `Module.Finite` instances expose the lattice structures in the recorded
  Borel-pair theorem, rather than substituting abstract abelian groups.
- The finite root set is `Φ`; `P : RootDatum Φ X X_*` and `hred` give its perfect
  integer pairing, coroots, reflections and reducedness. `hroot` identifies
  `P.root α` with the actual character `α.val`. `hpair` identifies composition
  of a cocharacter and character with the integer power of the identity of G_m.
  `aH`, `hconj`, and `hweights` say that these are exactly the nonzero character
  weights in the tangent Lie algebra under conjugation. These binders unpack
  the phrase "its root datum" in the node; they impose no choice of Borel or
  positive system. The finite lattice instances are precisely the corresponding
  two conclusions in `reductive_borel_pair_structure`.
- V is `ℚ ⊗[ℤ] X`, canonically X tensor ℚ with factors reversed. `hspan` is
  `Submodule.span ℚ (Set.range (fun α ↦ 1 ⊗ₜ P.root α)) = ⊤`.
- L is `Submodule ℤ V`, equivalently an additive subgroup of V.
  `[Module.Free ℤ L] [Module.Finite ℤ L]` express finite-rank freeness;
  `hrank` equates its integer rank with `Module.finrank ℚ V`.
- `hXL` places `1 ⊗ₜ χ` in L for every actual character χ.
  `hindex` states finiteness of `L / comap L.subtype (range (χ ↦ 1 ⊗ₜ χ))`.
  By `hXL`, that comap is exactly the image of X inside L, so this is L/X.
- `hintegral` quantifies over every `l : L` and `α : Φ`, requiring its rational
  coroot evaluation to equal the cast of some integer. The functional used is
  `((Int.castAddHom ℚ).toIntLinearMap.comp (P.coroot' α)).liftBaseChange ℚ`:
  the canonical rational extension of the recorded integer pairing, with no
  arbitrary functional or map introduced.

Conclusions, clause by clause:

- `HL`, `TL` and `iTL` are the required group schemes and torus inclusion.
  `IsSemisimpleGroupScheme HL.X`, `IsMaximalTorus iTL`, and the split-torus
  isomorphism give split semisimplicity and its split maximal torus.
- The existential commutativity witness on TL exposes the additive character
  group. `e : Additive (TL ⟶ G_m) ≃ₗ[ℤ] L` is the required identification.
- `f : HL ⟶ H` is a bundled group-scheme homomorphism;
  `Surjective f.hom.hom.left` is scheme surjectivity.
  `IsFinite (GrpObj.ker f.hom.hom).hom` is finiteness of the full scheme-theoretic
  kernel. The recorded group-scheme definition equates this with a finite
  dimensional coordinate algebra over F, including nonreduced kernels.
- For every commutative F-algebra A, every A-point x of this kernel and every
  A-point g of HL, the equality `(x ≫ kerι f) * g = g * (x ≫ kerι f)` expresses
  centrality. No reducedness, separability or rational-points-only substitute
  occurs. Test algebras are in the schemes' universe u, not an independent
  smaller universe; coordinate algebras and their tensor products fit there.
- `fT : TL ⟶ T`, `iTL ≫ f = fT ≫ iT`, and scheme surjectivity of fT say that
  f carries TL onto T, with the specified restriction, including inseparable maps.
- For every χ, `(e (Additive.ofMul (fT ≫ χ.toMul))).val = 1 ⊗ₜ χ` is precisely
  the pullback being the specified inclusion X → L, rather than some isomorphism.
- `IsIso f ↔ L = LinearMap.range (TensorProduct.mk ℤ ℚ _ 1)` is the literal
  equality criterion L=X, viewed as submodules of V. `IsIso f` in bundled group
  objects is equivalent to isomorphism of this group-scheme homomorphism.
- No characteristic, kernel smoothness, or order condition is assumed.

Dependency declarations read and used:

- `Field`, `Mathlib.Algebra.Field.Defs`; `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`. The algebraic-closure node records
  `AlgebraicClosure` and also explicitly names `IsAlgClosed`, the applicable
  component here; no chosen algebraic closure of F is required.
- `CategoryTheory.GrpObj`, `CategoryTheory.Grp`, and bundled homomorphisms,
  `Mathlib.CategoryTheory.Monoidal.Grp`; scheme kernels `GrpObj.ker`, `kerι`,
  and `AlgebraicGeometry.IsFinite` as documented in
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`, the recorded interface
  of `def-sc-group-scheme`.
- `AlgebraicGeometry.reductive_borel_pair_structure` and
  `semisimpleGroupScheme_isReductive`,
  `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveBorelPairStructure` (public import).
  Its full signature and docstring were read. The theorem's terminology is
  reused through `IsSemisimpleGroupScheme`, `ReductiveTorusCentralizer.IsMaximalTorus`,
  `MultiplicativeType.splitTorus`, `TorusCharacterTangent.weightSpace`, and
  Mathlib `RootDatum`; their defining source files were also read.
- Rational tensor extension uses `LinearMap.liftBaseChange` and the actual
  `RootPairing.coroot'` functional, as already used by the landed
  `simplyConnected_character_lattice` consumer. No private copies are defined.

The three other proof dependencies (`lem-sfb-root-datum-realization`,
`lem-sfb-semisimple-roots-span`, `lem-sfb-root-datum-isogeny-realization`) currently
have no Lean records or matches and supply no modules to import. They are not
statement prerequisites. Their full statements were read; the complete three-step
proof from the node is included in this declaration's docstring. The existing
Borel-pair proof dependency is publicly imported since it also supplies terminology.

Sources checked directly using pdftotext on the local Milne PDF: printed
pp.483--487 (Definitions 23.1--23.2, Proposition 23.5 including its centrality and
isomorphism proof, Theorem 23.9), p.501 (23.55--23.58), and pp.613--615
(C.28--C.35). The lattice argument and its prescribed inclusion agree exactly.

Edge cases checked before writing:

- Empty roots and rank zero: hspan forces V=0, L=0, and the criterion requires
  an isomorphism. No nonempty/Fintype/root-positive assumption is imposed.
- L equal to X: the criterion requires f to be an isomorphism and the character
  equation still specifies the identity inclusion.
- The SL₂ to PGL₂ central covering in characteristic 2 is allowed: μ₂ is not
  reduced, but its scheme-theoretic kernel is finite and commutes on every algebra.
- Positive characteristic dividing L/X and characteristic zero are both allowed;
  no exponent, prime or invertibility binder occurs.
- L as a subgroup and its quotient use real submodules; quotient finiteness does
  not silently assume L=X or replace finite index by finite generation.

Searches for an existing statement:

- `msearch.py leansearch`, query "central isogeny semisimple group character
  lattice enlargement": eight hits, character modules and central series of
  abstract groups, no algebraic group realization.
- `msearch.py leanfinder`, query "Realize a finite index integral enlargement of
  the character lattice of a semisimple algebraic group by a central isogeny":
  eight hits on finite representation characters, G₂, Hilbert 90 and Lie weights;
  none is the statement.
- `msearch.py loogle`, query "RootDatum, RootPairing, TensorProduct": no hits.
- `msearch.py grep`, query `central.isogen|lattice.enlarg|weightLattice|rootDatum`:
  two hits in Mathlib root-system definitions, which do not construct group schemes.
  The exact output records are retained in the sandbox `searches.jsonl`.
- `rg` on project `WeilConjectures/`, `Sheaf/`, and `dag/lean_names_upstream.json`
  with lattice-enlargement/central-isogeny/root-datum-realization patterns:
  existing central-isogeny properties and the simply-connected lattice consumer,
  but no realization statement. Search for the item id in `WeilConjectures/`
  returned no match. More general kernel/isogeny searches located the existing
  scheme-level kernel, finiteness and centrality conventions which were reused.

Validation: scompile.py compiled the sandbox and the actual library module cleanly
in 9.2 s and 7.0 s respectively, with no errors or warnings. Only the authorized
single-file wrapper was used. All binders are explicit with `autoImplicit false`.
No statement fault or STATEMENT-DISPUTED finding remains.

## Second reading by N5

Author's separate clause-by-clause rereading, with the original JSON and final Lean
source open; the maintainer supplies the independent review under the dispatcher
brief. The rereading checked the field and group hypotheses, the fixed split
maximal torus, actual characters/cocharacters, conjugation weights, rational root
span, finite-rank free L, rank equality, literal X containment, finite quotient,
all-root integrality, existence of HL/TL/e/f/fT, semisimplicity, split maximality,
scheme surjectivity, finite full kernel, all-algebra centrality, the commuting
restriction square, torus surjectivity, pointwise prescribed pullback and the
literal equality criterion. Every clause is rendered above. No additional Borel,
base, positivity, smooth-kernel or prime-to-characteristic hypothesis is present.
The `Module.Finite` mixins on X and X_* unpack the recorded root-datum convention,
not additional restrictions; freeness follows from that perfect pairing. Rechecked
that the quotient is formed inside L via comap of its actual subtype and that the
final equality is in the common ambient rationalization. No mismatch found and
no node correction or extra declaration was necessary.
