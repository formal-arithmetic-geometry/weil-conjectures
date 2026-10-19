## Worker report

The returned packet had an H3 mismatch: the Lean theorem treated the given completed-ring isomorphism as an arbitrary ring isomorphism over unrelated base maps, and its existential `ψY` and `ψX` were only constrained on the local-ring images.  I repaired the statement in `lean/Sheaf/TraceFormula/IsomorphismCompletionApproximation.lean` and updated the node's `lean.statement` verbatim.

The theorem `AlgebraicGeometry.isomorphism_completion_approximation` binds schemes `S X Y : Scheme.{u}`, structural maps `fX : X ⟶ S` and `fY : Y ⟶ S`, instances `IsLocallyNoetherian S`, `LocallyOfFiniteType fX`, `LocallyOfFiniteType fY`, points `x y s`, and equalities `hx : fX x = s`, `hy : fY y = s`.  The hypothesis `hGRing : IsGRing (S.presheaf.stalk s)` is the G-ring assumption.  The completed-ring isomorphism
`φ : AdicCompletion (maximalIdeal (Y.stalk y)) (Y.stalk y) ≃+* AdicCompletion (maximalIdeal (X.stalk x)) (X.stalk x)` has the source and target in the order of the node.  The added `hφ` is the missing `O_{S,s}`-algebra condition: after the canonical stalk maps from `S.stalk s` into the two stalks and the canonical algebra maps into their completions, the two composites into `X`'s completion are equal.

For every `N : ℕ` with `2 ≤ N`, the conclusion supplies `U : Scheme.{u}`, `u : U`, maps `p : U ⟶ X`, `q : U ⟶ Y`, pointed equalities `hp : p u = x`, `hq : q u = y`, and `p ≫ fX = q ≫ fY`.  It supplies ring homomorphisms `ψY` and `ψX` from the completed `Y` and `X` stalks to the completed `U` stalk.  The conjuncts `Etale p`, `Etale q`, `IsIso (p.residueFieldMap u)`, and `IsIso (q.residueFieldMap u)` render the two elementary étale-neighbourhood conditions.

The next two conjuncts state the canonical restriction equations: `ψY` after the completion algebra map equals the `q` stalk map transported along `Y.stalkCongr (.of_eq hq)`, and similarly `ψX` equals the transported `p` stalk map.  To remove the remaining arbitrariness in completion maps, two further conjuncts give their coordinatewise universal-property equations.  For every quotient level `n`, completed element `z`, and local element `a`, if `evalₐ` identifies `z` with the quotient class of `a`, then `evalₐ (ψY z)` is the quotient class of the transported `q`-stalk image of `a`; the analogous equation is stated for `ψX` and `p`.  These are the actual induced completion maps, rather than arbitrary ring homomorphisms agreeing only on a dense image.

Finally, for every completed `Y`-source element `a`, both maps to the completed `U` stalk have equal images in the quotient by the `N`-th power of the maximal ideal transported along the completion algebra map.  This is exactly the modulo-`m_u^N` commutative triangle of Stacks Tag 0CAV, with `ψX (φ a)` on the `X` leg.

Dependencies used in the module are the recorded Mathlib/project declarations: `AlgebraicGeometry.Scheme` (`Mathlib.AlgebraicGeometry.Scheme`), `AlgebraicGeometry.LocallyOfFiniteType` (`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`), `AlgebraicGeometry.Etale` (`Mathlib.AlgebraicGeometry.Morphisms.Etale`), `Scheme.residueField` and `Scheme.Hom.residueFieldMap` (`Mathlib.AlgebraicGeometry.ResidueField`), `AdicCompletion` (`Mathlib.RingTheory.AdicCompletion.Algebra`), and `IsGRing` (`Sheaf.RingTheory.GRing`).  No new definition node or dependency repair is needed.

I checked the edge cases `N = 2`, arbitrary larger finite `N`, zero and positive powers in the completion-coordinate clauses, zero elements, zero maximal ideals (fields), non-algebraically-closed residue fields, and nonreduced Artinian local stalks.  No extra nonemptiness, dimension, separatedness, smoothness, algebraic-closure, or field hypothesis was added.  The common-base equation and `hφ` retain the source's pointed-over-`S` and `O_{S,s}`-algebra requirements.

Searches rerun for the repair: `rg -n 'isomorphism_completion_approximation|0CAV|lemma-isomorphism-approximation|completed local'` in the literature, project source, and existing Lean found only this statement and the relative approximation callers; `rg -n 'stalkCongr|residueFieldMap|AdicCompletion'` found the recorded stalk/completion declarations; `msearch.py` LeanFinder/Loogle/grep searches for completed-local-ring approximation again found only generic étale/completion APIs and no matching theorem.  The source comparison is Stacks `more-morphisms.tex`, Tag 0CAV, lines 11071–11141: it explicitly requires an `O_{S,s}`-algebra isomorphism and canonical maps induced by the two pointed morphisms.

## Repair of the Lean rendering

The natural-language node is unchanged, so no §1(C) correction or `statement_change` is required. The returned H3 issue was the missing scalar-compatibility hypothesis and the unconstrained completion-map witnesses.  The corrected theorem adds `hφ` expressing that `φ` is an `O_{S,s}`-algebra isomorphism, and adds the finite-level `evalₐ` coordinate equations for `ψY` and `ψX`, while retaining every original hypothesis and conclusion clause.  The only node field changed is `lean`; the natural-language statement already requires scalar compatibility and the actual induced completion maps. No hypothesis or conclusion is added to that natural-language statement. No citer is edited.

## Second reading by NN

I reread the corrected node and module clause by clause.  `hφ` now has domain `S.presheaf.stalk s` on both sides, uses `stalkCongr` along `hx` and `hy`, and composes the structural stalk maps with the canonical completion algebra maps, so it cannot be satisfied by an isomorphism unrelated to the base.  The witness maps have the exact source and target completed stalks; `hp` and `hq` transport the stalk maps to those displayed points.  The two `evalₐ` conjuncts quantify all levels, completed elements, and local representatives, so the maps are the canonical completion maps.  The final congruence still quantifies every completed source element and uses the transported `N`-th maximal-ideal power.  The theorem proof remains statement-only (`sorry`) and all definitions have real data.

The proof docstring now writes out all seven DAG proof steps and their dependencies.
The already recorded proof interfaces `Sheaf.RingTheory.FlatLocalCompletionIso` and
`Sheaf.RingTheory.LocalCompletionQuotient` are imported non-publicly, along with the
Mathlib local completion, flatness, and unramified local-ring interfaces. The two
approximation/criterion proof dependencies currently have no Lean record and thus
have no module to import; they are cited by node id in the docstring.
