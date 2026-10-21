## Worker report

States `AlgebraicGeometry.exists_open_geometricallyIrreducible_finiteCover_linearSystem` in `lean/Sheaf/AlgebraicGeometry/BertiniFiniteCoverIrreducibleSystem.lean`. Its sole proof is `sorry`. No new definition, new node, dependency module, or statement correction is needed. The node copy changes only `lean`.

Source read: `literature/blueprint/main-20261015/blueprint/sec-deligne-laumon-general/sk-i-dl-general-real/lem-zl-bertini-finite-cover-curve.proof.md`, especially paragraph 3 and its surrounding construction. Also read Stacks `more-morphisms.tex`, `lemma-bertini-irreducible`, Tag 0G4F, including its four hypotheses and general-member conclusion. The module docstring reproduces all fifteen DAG proof steps, with their dependency IDs. All recorded modules for stated proof dependencies are imported without `public`, except modules also needed by the statement, which are public imports.

Hypothesis and clause correspondence:

| Node text | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type u) [Field k] [IsAlgClosed k]` |
| Scheme X over k | `(X : Scheme.{u}) [X.Over (Spec (.of k))]`, canonical structure morphism `X ↘ Spec (.of k)` |
| Smooth | `[Smooth (X ↘ Spec (.of k))]` |
| Connected, in particular nonempty | `[ConnectedSpace X]`, whose class includes nonemptiness |
| Affine | `[IsAffine X]` |
| Finite type | `[LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]` |
| Pure dimension d >= 2 | `(d : ℕ) (_hd : 2 ≤ d) (_hdim : X.IsPureDimension d)` |
| Finite étale π:T→X, T connected | `(T : Scheme.{u}) [ConnectedSpace T] (π : T ⟶ X) [IsFinite π] [Etale π]` |
| Nonempty finite set S in X(k) | `(S : Finset X) (_hS : S.Nonempty) (_hclosed : ∀ x ∈ S, IsClosed ({x} : Set X))` |
| Open complement X\S | `(U₀ : X.Opens) (_hU₀ : (U₀ : Set X) = (S : Set X)ᶜ)` |
| Invertible O_X-module L | `(L : X.Modules) [L.IsInvertible]` |
| Finite-dimensional vector space V | `(V : Type v) [AddCommGroup V] [Module k V]`, with a finite basis `(r : ℕ) (b : Module.Basis (Fin r) k V)` |
| k-linear ψ:V→Γ(X,L) | `(ψ : V →+ Γ(L, ⊤))` plus `_hlinear`, expressing scalar multiplication through `(X ↘ Spec (.of k)).appTop ((Scheme.ΓSpecIso (.of k)).inv c)` |
| Every ψ(v) vanishes on reduced S | `_hvan`: every x in S belongs to `(Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.support` |
| Restricted sections generate L on X\S | `hgen`: `Epi` of `freeHomEquiv.symm` for the canonically restricted basis sections, converted by `SheafOfModules.unitHomEquiv` |
| Associated map X\S→P(V) is an immersion | `[IsImmersion (@ProjectiveSpace.homOfGeneratingSections ... hgen)]` using that same family and the structure map `U₀.ι ≫ (X ↘ Spec (.of k))` |
| H_v = Z(ψ(v)) | `(Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subscheme`, with its canonical `subschemeι` into X |
| T_v = T×_X H_v | `pullback π (Scheme.Modules.homOfGlobalSection L (ψ v)).zeroLocus.subschemeι`; its map to H_v is `pullback.snd` |
| Nonempty Zariski open U_irr in A(V) | `∃ U : (Spec (.of (MvPolynomial (Fin r) k))).Opens, (U : Set _).Nonempty ∧ ...` |
| For every v in U_irr(k) | `∀ v : V`, followed by `Set.range (Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom (RingHom.id k) (fun i ↦ b.repr v i)))) ⊆ (U : Set _)` |
| H_v geometrically irreducible | First `GeometricallyIrreducible` conjunct, applied to H_v's inclusion followed by X's structure map |
| T_v geometrically irreducible | Second `GeometricallyIrreducible` conjunct, applied to `pullback.snd ≫ H_v.subschemeι ≫ (X ↘ Spec (.of k))` |
| If H_v smooth over k then T_v smooth | Implication from `Smooth` of H_v's structure map to `Smooth` of the above T_v structure map |
| T_v→H_v finite étale, both connected in that case | The remaining conditional conjuncts are `IsFinite (pullback.snd ...)`, `Etale (pullback.snd ...)`, `ConnectedSpace H_v`, and `ConnectedSpace T_v` |

The closed-point rendering of S is equivalent to the stated rational-point rendering, not an additional geometric restriction: over an algebraically closed k every closed point of a finite-type k-scheme has residue field k (the Nullstellensatz), and a k-point is a closed point. The structure morphism identifies its residue-field map uniquely, so finite subsets correspond. Since S has the reduced structure, vanishing on it is precisely vanishing in each residue field, equivalently membership in the section's zero-locus support. No nonreduced base-locus assumption has been made: the common zero scheme may be thicker than S.

`U₀` and its set equality merely name the canonical complement; there is exactly one such open. A basis is coordinate data, not an additional mathematical assumption on a finite-dimensional vector space. In these coordinates A(V) is `Spec k[x_i]`; its k-point associated to v is evaluation at `b.repr v`. Thus the conclusion only quantifies over k-points, exactly as the node does, rather than adding an extension-field conclusion. Projective coordinates use `ULift.{u} (Fin r)` so the existing projective construction has the correct scheme universe. The lift is a bijection on the same finite coordinate set. Using an additive map together with `_hlinear` writes out the exact canonical k-linear structure without a local scalar instance or a `let` inside the statement.

Generation can be checked on the basis family because every vector is a finite k-linear combination of basis vectors and restriction respects that action. The restricted module is the prescribed `(Scheme.Modules.tensorPullback U₀.ι).obj L`. Its invertibility is supplied directly from the existing adjunction comparison with native pullback and `Scheme.Modules.IsInvertible.of_iso`; it is not an added hypothesis or postponed helper. All section restrictions use `Scheme.Modules.tensorSectionsUnit`, the canonical normalized tensor-pullback unit.

Statement dependency declarations read and used:

- `def-weil-pbc-scheme-conventions` and `def-weil-scheme-morphism-properties` are convention nodes with no declaration. Their named Mathlib properties are used: `Scheme`, `IsAffine`, `LocallyOfFiniteType`, `QuasiCompact`, `Smooth`, `IsFinite`, `Etale`, and `IsImmersion`. Read the relevant Mathlib class signatures and docstrings.
- `def-sc-invertible-module`: `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, `AlgebraicGeometry.Scheme.Modules.IsInvertible`; read its rank-one local triviality class and `of_iso`.
- `def-weil-pbc-generating-sections`: `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`, `SheafOfModules.GeneratingSections`; read its `s` and `epi : Epi (M.freeHomEquiv.symm s)` fields. We use precisely that epimorphism predicate.
- `def-weil-pbc-morphism-to-projective-space-by-sections`: `Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections`, `AlgebraicGeometry.ProjectiveSpace.homOfGeneratingSections`; read the full signature, construction and classification docstrings. The precise recorded morphism is used, with no arbitrary map supplied in its place.
- `def-pc-zero-scheme`: `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`, `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`; read its definition and docstring explaining the dual-section ideal and local equation. `homOfGlobalSection` turns each actual section into the required O_X-module morphism.
- `def-pc-base-change`: `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`; read its definitions and comparison statements. The node's explicit convention is the chosen `CategoryTheory.Limits.pullback` with `pullback.snd` for the projection to the new base; these are used for T_v and its map to H_v.
- `def-weil-connected-scheme`: `Mathlib.Topology.Connected.Basic`, `ConnectedSpace`; read the nonempty preconnected class at line 705.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral` imports `Mathlib.AlgebraicGeometry.Geometrically.Irreducible`, whose `AlgebraicGeometry.GeometricallyIrreducible` class is used. Its definition tests irreducibility after field base change, including nonemptiness.
- `def-weil-pure-dimension`: `Sheaf.AlgebraicGeometry.PureDimension`, `AlgebraicGeometry.Scheme.IsPureDimension`; read its full definition using the dimensions of irreducible components.

Edge cases checked: d=2 is included by `2 ≤ d`. The empty schemes X and T are excluded exactly by the node's connectedness. S is explicitly nonempty; its complement is not separately assumed nonempty. V=0 and an empty basis are permitted by the binders, leaving the actual generation and immersion hypotheses to rule out impossible instances. An arbitrary kernel of ψ is allowed. The zero vector is not silently discarded. The identity finite étale cover is included. There is no characteristic restriction, separability condition on k, degree restriction on the cover, or smoothness hypothesis imposed on H_v before the final implication. Universe v for V is independent of u; the finite basis gives all affine/projective coordinates without identifying those universes. No `STATEMENT-DISPUTED` remains and no statement correction was made.

Searches actually run:

- `msearch.py ... leanfinder "Bertini general sections geometrically irreducible simultaneously finite etale cover"`: eight hits, on étale sites, étale loci, standard smoothness and normalization; no simultaneous Bertini statement.
- `msearch.py ... loogle "AlgebraicGeometry.GeometricallyIrreducible, AlgebraicGeometry.Etale"`: zero hits.
- `msearch.py ... grep "Bertini|bertini" AlgebraicGeometry`: zero Mathlib hits.
- `rg -n 'bertini|Bertini|finite.cover.*irreducible|IrreducibleSystem' lean/Sheaf/AlgebraicGeometry lean/WeilConjectures/AlgebraicGeometry`: found the existing individual Bertini irreducibility and smoothness modules, the universal family and auxiliary incidence lemmas, but no simultaneous finite-cover statement. Read `BertiniIrreducibleMember` and the relevant signatures and helpers in `BertiniSmoothMember`; the former requires codimension-two witnesses, and the latter gives smoothness, so neither states this item.
- `rg -n 'lem-zl-bertini-finite-cover-irreducible-system' lean/WeilConjectures`: no existing declaration.
- `rg -n 'BertiniFiniteCoverIrreducible|exists_open_geometricallyIrreducible_finiteCover' lean/WeilConjectures lean/Sheaf dag/lean_names_upstream.json`: no name collision before writing.
- Additional source searches for `tensorSectionsUnit`, tensor-pullback invertibility, scalar actions on sections, finite sets of points, `fieldPoints`, and restriction declarations identified the canonical APIs above. The first compile required a Scheme annotation for the pullback inside `ConnectedSpace`; a later compile found a docstring closing-space warning, which was fixed. No mathematical hypothesis changed during these elaboration fixes.

Validation: all compilation uses the prescribed `scompile.py` server wrapper, with the normal 60-second limit. The final clean compile and delivery preflight are recorded by the delivery wrapper. No direct git command, live source edit, global build, or local Lean compile was run.

## Second reading by O4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
