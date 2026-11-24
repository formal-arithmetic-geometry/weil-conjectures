import Lean

open Lean Elab Command

syntax (name := mdaFieldsCmd) "#mda_fields " ident : command

elab_rules : command
  | `(#mda_fields $id:ident) => do
      let name := id.getId
      let fields := getStructureFields (← getEnv) name
      for i in [:fields.size] do
        logInfo m!"MDA_FIELD {name} {i} {fields[i]!}"
