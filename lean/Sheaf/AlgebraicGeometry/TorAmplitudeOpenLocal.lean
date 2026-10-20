/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal
import all WeilConjectures.AlgebraicGeometry.TorAmplitudeOpenLocal

/-! # Locality of a fixed Tor amplitude interval

The theorem `AlgebraicGeometry.torAmplitude_of_open_neighbourhoods` and its complete
K-flat model and open-cover proof are provided by the upstream module. This compatibility
import restores the former Sheaf path after the upstream synchronization removed the
duplicate Sheaf implementations. It uses the current derived pullback and derived tensor
definitions. The proof-only `import all` preserves access to the existing private model and
restriction lemmas for consumers using `import all` on this path.

Source: Stacks Project, Cohomology of Sheaves, Lemma 09U9
(cohomology-lemma-tor-amplitude-stalk).
(blueprint: lem-pc-tor-amplitude-open-local).
-/

@[expose] public section
