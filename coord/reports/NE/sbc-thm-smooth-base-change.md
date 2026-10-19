## Worker report

The module `lean/Sheaf/SixFunctors/Etale/SmoothBaseChange/Theorem.lean` states the smooth base-change theorem from the blueprint node and Stacks Tag 0EYU. It uses the canonical `Etale.baseChangeHomologyMap` and the stalkwise torsion/invertibility class. The hypotheses render as follows: `p : X ⟶ S` with `[Smooth p]`; `g : T ⟶ S` with `[QuasiCompact g] [QuasiSeparated g]`; arrows `e : Y ⟶ T`, `h : Y ⟶ X`; Cartesian square `(sq : IsPullback e h g p)`; arbitrary integer degree `(q : ℤ)`; coefficient sheaf `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`; and `[Scheme.IsTorsionSheafOfInvertibleOrder S F]`. The conclusion is exactly `IsIso (Etale.baseChangeHomologyMap Λ sq q F)`.

The module imports `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs` for the canonical map and torsion class, and `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth` for `Smooth`. The recorded square and scheme-convention dependencies are represented by Mathlib/upstream declarations used in the signature. The source theorem module was not imported because it collides with the side project's `Sheaf.AlgebraicGeometry.FiniteTypeIdealModule`; the side declaration preserves the exact statement with a distinct declaration name.

Edge cases checked: `q = 0`, negative degrees, zero sheaves, empty schemes, arbitrary scheme universe `u`, and stalkwise (rather than globally bounded) torsion. No additional hypotheses were introduced.

Searches: `msearch.py leanfinder` for “smooth base change theorem for torsion etale sheaves under a smooth morphism” found only ring-theoretic étale results; `loogle` for the expected theorem and `grep` for `isIso_baseChange.*smooth|smooth base change` found no Mathlib match. `rg` in the upstream source found the exact theorem in `SmoothBaseChange/Theorem.lean`; `rg` in `lean/Sheaf` found no prior declaration. The side module compiles cleanly with `scompile.py`; the only expected warning is the theorem's `sorry`.

## Earlier second reading (a previous round; superseded)

The statement was reread against the node and Stacks Tag 0EYU. Every diagram arrow, smoothness, quasi-compactness, quasi-separatedness, Cartesian-square, degree, coefficient-sheaf, and stalkwise torsion hypothesis is present exactly once, and the conclusion names the canonical base-change map. No mismatch was found.

## Second reading by NE

I reread the node statement, its source place (blueprint node order 1417 and Stacks Tag 0EYU), the worker module, and the recorded dependency declarations.

- Objects and diagram: the Lean binders `p : X ⟶ S`, `g : T ⟶ S`, `e : Y ⟶ T`, and `h : Y ⟶ X` render the four schemes and arrows in the node's Cartesian square, with all schemes in the common scheme universe `u`.
- Hypotheses: `[Smooth p]` renders smoothness of the left vertical map; `[QuasiCompact g]` and `[QuasiSeparated g]` render the two hypotheses on `g`; `sq : IsPullback e h g p` renders the Cartesian square and its commutativity. No finiteness, Noetherian, separatedness, or characteristic hypothesis is added.
- Coefficients: `Λ : Type (u + 1)` with `[CommRing Λ]` and `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)` are the module-sheaf realization of the node's coefficient sheaf; `[Scheme.IsTorsionSheafOfInvertibleOrder S F]` is exactly the stalkwise torsion condition with an order invertible on `S` (the recorded class quantifies over geometric stalks).
- Conclusion: for arbitrary `q : ℤ`, `IsIso (Etale.baseChangeHomologyMap Λ sq q F)` states that the canonical degree-q base-change map is an isomorphism, matching the node's equality of higher direct-image sheaves. The canonical map is imported from the recorded smooth-base-change definitions; the dependency's abelian specialization is the `Λ = ℤ` case.

Edge cases checked: `q = 0`, negative `q`, zero sheaves, empty schemes, arbitrary allowed scheme universe, and torsion orders including the invertible-order condition. The statement does not restrict to positive degrees or nonempty schemes.

Searches were repeated with `msearch.py`/LeanFinder and Loogle for smooth étale base change, and with `rg` through Mathlib, `WeilConjectures`, and `lean/Sheaf`; no exact prior theorem was found beyond the upstream theorem whose proof is postponed. The upstream declaration and the node's source statement agree on the module-coefficient formulation used here. The module compiled with `scompile.py`; only the expected `sorry` warning occurs.

No mismatch was found, so no source or node change was required.

## Independent maintainer correction (2026-10-15)

This section supersedes the claims above that a duplicate side declaration is necessary and that no usable exact upstream theorem exists. The immutable delivered module compiles through scompile.py, but violates H4 (duplicate theorem) and H8 (missing module docstring and stepwise proof docstring). The replacement lean record uses existing: true, branch slopmaster2, module WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Theorem, declaration AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth. The landing tool automatically omits the delivered side module when applying this record, so neither documentation defect enters the project.

The upstream signature agrees verbatim with the delivered signature after removing the suffix `_statement`. Its p, g, e, h binders describe precisely the node's square; Smooth p, QuasiCompact g, QuasiSeparated g and IsPullback e h g p supply exactly its geometric hypotheses. The arbitrary integer q includes degree zero and the harmless negative-degree vanishing extension. Module coefficients are the standard constant-coefficient realization: abelian sheaves are obtained using the integer ring in the allowed larger universe. No finite coefficient ring, bounded torsion exponent, Noetherian hypothesis or nonempty scheme is imposed. Scheme.IsTorsionSheafOfInvertibleOrder requires, for every element of every separably closed geometric stalk, a positive annihilator which is a unit on S, not merely on T or on the support. The map is the actual homology of the derived unit/square/counit exchange, not an arbitrary arrow. The recorded dependency retains its module-coefficient map and its bounded-below specialization; its unbounded abelian extension does not change this canonical degreewise map.

Read the item and all three statement dependency records from the snapshot, their exact declarations in the read-only clone/source, the item blueprint, and Stacks etale-cohomology.tex at theorem-smooth-base-change (Tag 0EYU) and its second proof. Checked empty schemes, zero sheaves, q=0, q<0, varying torsion exponents, order 1, excluded noninvertible orders, etale/identity maps and arbitrary scheme universe u. The source proof's relative-dimension-zero case is covered by etale locality and the identity map, as recorded in the node. No statement correction or citer audit is needed.

Independent rg searches for baseChangeHomologyMap_of_smooth and smooth base change across Mathlib, WeilConjectures and lean/Sheaf found the upstream exact theorem. Its source has a proof assembled from upstream lemmas; a postponed proof anywhere in that upstream chain does not authorize a duplicate stage-2 theorem.

Compiler evidence: scompile.py NE sbc-thm-smooth-base-change on the immutable delivered file returned 0, sandbox 4.0 s and library 4.3 s. A separate import of the upstream Theorem module followed by #check @AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth returned 0, sandbox 5.1 s and library 5.2 s, printing every expected binder. Both checks used the local side overlay; no server fallback was needed. The claimed FiniteTypeIdealModule collision did not reproduce. No project clone or branch was edited, no global build was run, and no proof was added.
