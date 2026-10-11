## Worker report

The module states `AlgebraicGeometry.Scheme.Modules.exists_quasiCoherent_extension_of_quasiCompact_open` in `Sheaf.AlgebraicGeometry.QuasiCoherentExtensionQcOpen`. The scheme is `X : Scheme.{u}` and the open subscheme is `U : X.Opens`; its inclusion is `U.ι`, with the node's quasi-compactness hypothesis rendered as `hU : QuasiCompact U.ι`. The given modules are `F : X.Modules` and `G : U.toScheme.Modules`, with hypotheses `[F.IsQuasicoherent]` and `[G.IsQuasicoherent]`. The map in the node is rendered as `φ : G ⟶ (restrictFunctor U.ι).obj F`, using Mathlib's restriction functor for the open immersion.

The conclusion is rendered as `∃ (H : X.Modules), H.IsQuasicoherent ∧ ∃ (ψ : H ⟶ F) (α : (restrictFunctor U.ι).obj H ≅ G), α.hom ≫ φ = (restrictFunctor U.ι).map ψ`. Thus `H` is quasi-coherent on `X`, `ψ` is the required map to `F`, `α` is the required isomorphism from the restriction of `H` to `G`, and the final equality is exactly `φ ∘ α = ψ|_U` in categorical composition order.

Dependencies used are Mathlib's `AlgebraicGeometry.Scheme`/`Scheme.Hom` for schemes and morphisms, `AlgebraicGeometry.QuasiCompact` for `QuasiCompact`, Mathlib `Scheme.Modules` and `Scheme.Modules.restrictFunctor` for sheaves of modules and restriction, and Mathlib `SheafOfModules.IsQuasicoherent` (imported through `Sheaf.AlgebraicGeometry.Coherent`) for the quasi-coherence predicates recorded by `pqf-def-coherent` and `def-weil-sheaf-of-modules-category`.

Edge cases checked: `U` may be empty (the theorem has no nonemptiness assumption), `F` and `G` may be zero modules, and the universe of the open's module category is the same `u` as the scheme universe. No additional separatedness, finite-presentation, or field hypotheses were added.

Searches for an existing declaration: `msearch.py leanfinder` for quasi-coherent extension across a quasi-compact open returned eight hits including `exists_of_res_eq_of_qcqs`, `Scheme.Modules.restrict`, and quasi-coherence infrastructure, with no module extension theorem; `msearch.py loogle` for `SheafOfModules.IsQuasicoherent` returned only Mathlib quasi-coherence and pushforward infrastructure, not this extension statement; `msearch.py grep` of Mathlib `AlgebraicGeometry/Modules` for `extend|extension` returned only `TopCat.Sheaf.extend_hom_app` at Tilde.lean:304, not an extension theorem for quasi-compact open immersions; `rg` over `WeilConjectures/` and project `lean/Sheaf` found no matching extension declaration. The node's recorded Mathlib searches likewise report no match.

No `STATEMENT-DISPUTED` issue or node fault was found.

## Earlier second reading (a previous round; superseded)

Pending independent second reading by the next worker; the author has not supplied an independent review.

## Second reading by M1

Independent reading of the node, the delivered Lean module, all five statement
 dependencies, and Stacks Properties Lemma 01PE (lemma-extend-trivial), part (3)
and proof. The repository's literature/stacks-project/properties.tex is absent on
this machine; I read the available Stacks source at
/home/ubuntu/c1-stacks-review/properties.tex, lines 2787–2843, including the
section introduction and chapter introduction. There are no standing Noetherian,
separatedness, field, or finiteness assumptions here.

Object, hypothesis, and conclusion checklist (all verdicts: exact):

- Scheme X: `(X : Scheme.{u})`, the recorded Mathlib Scheme declaration,
  read in Scheme.lean:42 (locally affine locally ringed space).
- Open subscheme U and its inclusion j: `(U : X.Opens)`, `U.toScheme`, `U.ι`.
  Read Restrict.lean:46–57: these are the open restriction, its inclusion,
  and the derived open-immersion instance. No extra immersion hypothesis.
- Quasi-compact inclusion: `(hU : QuasiCompact U.ι)`. Read the convention
  node and its named Mathlib notion in Morphisms/QuasiCompact.lean:43;
  quasiCompact_iff_forall_isAffineOpen:97 identifies it with the node's
  compactness of U intersected with each affine open. It is not compactness
  of U alone and is not a hollow identity-morphism hypothesis.
- O_X-module F: `(F : X.Modules)`; quasi-coherence `[F.IsQuasicoherent]`.
- O_U-module G: `(G : U.toScheme.Modules)`; quasi-coherence
  `[G.IsQuasicoherent]`. Read Modules/Sheaf.lean:40 and SheafOfModules at
  Algebra/Category/ModuleCat/Sheaf.lean:33 and its morphisms: modules with
  semilinear restrictions, and sectionwise linear morphisms, as required by
  def-weil-sheaf-of-modules-category. Read pqf-def-coherent and its module
  Coherent.lean: quasi-coherence is the shared Mathlib IsQuasicoherent,
  read in Sheaf/Quasicoherent.lean:251 (local presentations), equivalent
  on schemes to the node's affine-local associated-module description.
- Restriction F|_U: `(restrictFunctor U.ι).obj F`. Read the definition at
  Modules/Sheaf.lean:348 and restrictAppIso:360: sections on an open of U
  are sections on its image in X, with the structure-ring identification.
  This is restriction, not a replacement notion of module pullback.
- Given linear map: `(φ : G ⟶ (restrictFunctor U.ι).obj F)`.
- Extended quasi-coherent module: `∃ (H : X.Modules), H.IsQuasicoherent ∧`.
- Extended linear map: `∃ (ψ : H ⟶ F)`.
- Identification over U: `(α : (restrictFunctor U.ι).obj H ≅ G)`.
  The source's equality H|_U = G is its explicit identification in the proof;
  the node correctly spells it as an isomorphism.
- Compatibility: `α.hom ≫ φ = (restrictFunctor U.ι).map ψ`, exactly
  φ composed with α equals ψ restricted to U, with categorical composition
  in the correct order. H, then ψ and α, are existential after all inputs.

Edge cases: U = empty and X = empty are allowed; there is no Nonempty
binder. Zero F and G are allowed, and φ is arbitrary (no mono/epi condition).
No index set or n occurs. Rings have arbitrary characteristic and need not
be fields. The explicit universe u is arbitrary and uses the project's
standard Scheme.{u}/X.Modules carrier, with the same universe on U; it
imposes no extra universe bound or smaller test-object quantification.

Independent searches:

- msearch leanfinder: "extend a morphism of quasicoherent modules from a
  quasi compact open subset" returned eight hits, principally extension
  of structure-sheaf sections (exists_of_res_eq_of_qcqs and variants),
  not extension of modules and a prescribed map.
- msearch loogle: "AlgebraicGeometry.Scheme.Modules.restrictFunctor"
  returned twelve restriction/adjunction/composition/stalk declarations;
  none states this extension result.
- msearch leansearch: "A quasi coherent module with a map into the
  restriction of another extends from a quasi compact open immersion"
  was unavailable (Internal Server Error); no verdict inferred from it.
- msearch grep: "quasiCoherent.*extension|extension.*quasiCompact|extend.*[Mm]odule"
  found unrelated algebraic module extensions, no matching scheme theorem.
- Direct rg for quasi-coherent extension phrases and restrictFunctor
  existential/isomorphism signatures in Mathlib module files, source
  WeilConjectures, and project lean/Sheaf. Opened project
  Modules/QuasicoherentExtension.lean: isQuasicoherent_of_shortExact is
  closure under short exact extensions, not this theorem. Opened source
  Compactification/FiniteTypeExtension.lean: finite-type ideal extensions
  on qcqs schemes are a different, specialized statement. No duplicate.

No new nodes or dependency modules are present or needed, and no statement
correction is present or needed. No hollow definition occurs; the sole
statement has a sorry proof, as stage 2 requires. All variables and the
universe are explicitly bound. The node's lean.statement equals the file's
signature verbatim. Source and blueprint docstrings and line width checked.

Mismatch repaired: the proof docstring omitted the named DAG dependencies
and direct-sum quasi-coherence justification. Added those references and
that step; preserved the complete theorem signature and node record.
The original file compiled cleanly on the server; the repaired file is
validated again by the delivery dry run and delivery compile.

## Reviewer fix (R-qeo1430)

Moved the statement to the carrier the STATE line EXTENSION ACROSS A QUASI-COMPACT OPEN prescribes (H1 ef7bad70c, K1 e123f1be9): `F`, `H : SheafOfModules.{u} (moduleRings X.toRingedSpace)`, `G` on `(moduleRings X.toRingedSpace).over U`, `φ : G ⟶ F.over U`, `α : H.over U ≅ G`, compatibility `(SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).map ψ = α.hom ≫ φ` (H4: the delivered `X.Modules`/`restrictFunctor U.ι` was a second carrier). The hypothesis stays `hU : QuasiCompact U.ι` with `X` an arbitrary scheme, as the node (01PE) says: the siblings' qcqs `X` with `IsCompact U` is the special case and would strengthen the hypotheses.
