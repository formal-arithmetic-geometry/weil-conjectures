## Worker report

The module `Sheaf.RingTheory.CompletedIdealGeneratorFibre` states
`AdicCompletion.exists_completedIdeal_generatorFibre`, with the sole proof `sorry`.
It introduces no definitions, axioms, auxiliary theorems, or new DAG nodes. The
node is unchanged except for its `lean` record. No statement fault or dispute was
found. There is no repair note for this item.

Clause-by-clause correspondence (write `m = maximalIdeal R`, `S = AdicCompletion m R`,
`c = algebraMap R S`, `J = I.map c`, and `n = m.map c` in this report only):

- Commutative Noetherian local ring: `{R : Type u} [CommRing R]
  [IsNoetherianRing R] [IsLocalRing R]`, with explicitly declared universe `u`.
- Ideal contained in the maximal ideal and finitely generated: `(I : Ideal R)
  (hI : I ≤ maximalIdeal R) (hIfg : I.FG)`. Both hypotheses are retained even
  though finite generation also follows from Noetherianity.
- The canonical completion and its map are exactly Mathlib's `AdicCompletion m R`
  and `algebraMap R S`; this algebra map is the compatible residue classes
  (`AdicCompletion.algebraMap_apply`, with `AdicCompletion.of`). Index zero in
  Mathlib contributes the unique element of the zero quotient, so including it
  gives the same inverse limit as the node's indices at least one.
- The extended ideals `J` and `n` are literally `Ideal.map` along this map.
- The completed ideal is `AdicCompletion m I`, where `I` is the ideal's subtype
  with its existing R-module structure. Its S-module structure is the existing
  `AdicCompletion.module`: at index q the action is multiplication of quotient
  coordinates, as specified by `AdicCompletion.smul` and `smul_eval`.
- The first existential gives `α : AdicCompletion m I ≃ₗ[S] J`.
  The first conjunct says its composite with `J ↪ S` equals the completed
  inclusion pointwise: `(α y : S) = AdicCompletion.map m I.subtype y`.
  Thus this is the isomorphism induced by completion of the inclusion, rather
  than an unspecified isomorphism.
- The second conjunct gives its required formula for every `a : I`:
  `(α (AdicCompletion.of m I a) : S) = c (a : R)`.
- The third conjunct is set equality `α '' ↑(m • (⊤ : Submodule R
  (AdicCompletion m I))) = ↑(n • (⊤ : Submodule S J))`.
  This uses the R-submodule of the completed ideal on the left and the
  S-submodule of J on the right, precisely the two submodules in the node.
- The residue-field identification is supplied explicitly by `e : (R ⧸ m) ≃+*
  (S ⧸ n)`. Its characterization on every `s : S` is
  `e.symm (Ideal.Quotient.mk n s) = AdicCompletion.evalOneₐ m s`.
  This fixes the canonical identification by first-coordinate projection,
  including its direction; it excludes an arbitrary automorphism of the residue field.
- The last existential gives `β : (I ⧸ m • ⊤) →ₛₗ[e.toRingHom] (J ⧸ n • ⊤)`,
  with `Function.Bijective β`. These quotient modules use Mathlib's existing
  `Module (R ⧸ m) (I ⧸ m • ⊤)` and `Module (S ⧸ n) (J ⧸ n • ⊤)` instances.
  Semilinearity along the characterized ring isomorphism e means exactly
  k-linearity after identifying `S/n` with `k = R/m`. A bijective semilinear
  map along this ring isomorphism is the stated vector-space isomorphism.
  R/m is a field because m is maximal; e identifies S/n with that field.
  This encoding needs no chosen scalar-transport instance or private definition.
- The final formula, for every `a : I`, is
  `β (Submodule.Quotient.mk a) = Submodule.Quotient.mk (α (AdicCompletion.of m I a))`.
  By the preceding formula for α, the right-hand side is exactly `[c(a)]` in
  `J/nJ`. The formula on all representatives fixes the canonical map.

Dependencies used and read:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (the abbreviation `IsNoetherian R R`, with docstring
  saying every ideal is finitely generated). Its recorded module is public imported.
- `def-weil-pbc-adic-completion`: `Mathlib.RingTheory.AdicCompletion.Basic`,
  `AdicCompletion` (compatible quotient families), `AdicCompletion.of`, and
  `AdicCompletion.eval`. Its recorded module is public imported.
  The ring/algebra and coordinatewise completed-module action are the existing
  `AdicCompletion.instCommRing`, `instAlgebra`, `module`, and `evalOneₐ` in
  `Mathlib.RingTheory.AdicCompletion.Algebra`, publicly available through
  `Mathlib.RingTheory.AdicCompletion.Functoriality`. The latter's `map` is the
  completed inclusion used in the statement, and has the full S-linear signature.
- `Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs` supplies the existing local-ring
  maximal ideal. The quotient scalar modules are Mathlib's existing instances in
  `Mathlib.Algebra.Module.Torsion.Basic`, imported through the completion algebra.
- The stated proof dependencies are imported privately, by their recorded
  Mathlib matches: `Mathlib.RingTheory.AdicCompletion.Exactness`
  (`map_injective`, `map_exact`, `map_surjective`);
  `Mathlib.RingTheory.AdicCompletion.AsTensorProduct`
  (`ofTensorProductEquivOfFiniteNoetherian`, `ofTensorProduct_tmul`,
  `ofTensorProduct_naturality`); and `Mathlib.RingTheory.AdicCompletion.LocalRing`
  (including its public dependency `Completeness`, with `isAdicComplete`,
  `pow_smul_top_eq_ker_eval`, `ker_evalOneₐ_eq_map`; and the existing
  `evalOneₐ_surjective`, `evalOneₐ_comp_algebraMap_eq_mk`, `isAdicComplete_self`).
  No project dependency interface needs repair.

Sources read: `literature/stacks-project/algebra.tex`, lemma-completion-tensor
(Tag 00MA), parts (2) and (3), and lemma-hathat-finitely-generated (Tag 05GG),
part (2). The source gives exactness, the tensor comparison, and the quotient
calculation used by the node. The latest blueprint's local-term-locality statement
and proof were also read: this auxiliary completion lemma belongs to the inherited
DAG algebra route, rather than being the blueprint unit's own statement.
The theorem docstring carries all four proof steps and names their DAG dependencies.

Edge cases checked mathematically before drafting:

- `I = 0`: both completed ideals and generator quotients are zero; all maps and
  submodule images have the specified values.
- R a field: m = 0 forces I = 0; completion is R and the residue isomorphism is
  the canonical identity under the quotient identifications.
- Artinian local R (including `k[ε]/(ε²)`, `I = (ε)`): the nilpotent-adic completion
  is R; α and the generator map reduce to the original ideal and its quotient.
- A DVR with `I = m^d`, d at least one: its generator space and that of the
  extended ideal are one-dimensional over the same residue field.
- Mixed and positive characteristic are unrestricted. No domain, reducedness,
  nonzero ideal, positive dimension, or chosen generating family is assumed.
  The zero ring is already excluded by the source's proper maximal ideal and
  residue-field convention, as by Mathlib's `IsLocalRing`.

Searches actually run using `msearch.py ND lem-trf-completed-ideal-generator-fibre`:

- LeanFinder: "Completion of a finite ideal identifies with its extended ideal and
  induces an isomorphism I/mI to IS/mS IS". Eight hits, including `piEquivFin`,
  `ofAlgEquiv`, `ofLinearEquiv_apply`, and a ramification quotient equivalence;
  no arbitrary-ideal completed-inclusion and generator-space theorem.
- Loogle: `AdicCompletion, Ideal.map`. Five hits: `ker_evalOneₐ_eq_map`,
  `isAdicComplete_self`, `isMaximal_map_of_le`, `maximalIdeal_eq_map`,
  `maximalIdeal_eq_map_of_fg`. These provide ingredients, not the whole statement.
- Mathlib grep: `quotient.*[Ee]quiv|[Ee]quiv.*quotient|map_injective`, restricted to
  `RingTheory/AdicCompletion`. Nine hits in AsTensorProduct, Exactness, Algebra,
  and Functoriality; none states all clauses for an arbitrary finite ideal.
- LeanSearch: "The completion of a finite ideal in a Noetherian local ring
  identifies with the extended ideal and preserves I modulo the maximal ideal
  times I". Eight hits including `AdicCompletion`, `instCommRing`, `module`,
  `subring`, `IsAdicComplete`, `instAlgebra`, and tensor-equivalence API;
  no exact statement. An earlier broader LeanSearch query asked for the same
  completed-ideal and residue-generator isomorphism.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `completedIdeal|completed_ideal|ideal.*[Gg]enerator|generator.*[Ff]ibre|completion.*[Ii]deal`,
  followed by the narrower
  `completedIdeal|idealCompletionEquiv|completed_ideal|completedIdealGenerator|completion.*[Gg]enerator`
  (also in `dag/lean_names_upstream.json`). The matches concern other constructions
  such as completed blow-up ideals, cotangent maximal-ideal rank, and regular-kernel
  preservation; none states this arbitrary-ideal comparison with its maps.
- Direct grep of the item id in `lean/WeilConjectures`: no match.
- Direct full-name search for `exists_completedIdeal_generatorFibre` in Mathlib,
  `lean/WeilConjectures`, and `lean/Sheaf`: no existing declaration.

Validation: the final module passes the prescribed `scompile.py` in both sandbox
and library module mode, with no errors or non-sorry warnings. Auto-bound implicits
are disabled, all declarations use explicitly bound variables and universe u,
and every Lean line is at most 100 characters. Initial compilation identified
module visibility imports and two elaboration issues (set coercion at the ideal
product and inference of inverse ring maps for a bundled semilinear equivalence).
The final statement uses an explicitly typed submodule coercion and the equivalent
bijective-semilinear-map encoding; these change no mathematical clause.

## Second reading by ND

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
