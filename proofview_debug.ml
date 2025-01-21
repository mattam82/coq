
(** {7 Debugging} *)
module Debug : sig
  val pr_goal : string -> 'a tactic -> 'a tactic
  val pr_econstr : EConstr.t -> 'a tactic -> 'a tactic
end


module Debug = struct
    let pr_goal s tac =
      let open Goal in
      enter begin fun gl ->
        Feedback.msg_debug Pp.(str s ++ str": " ++
          Printer.pr_named_context_of (env gl) (sigma gl) ++ fnl () ++
          str"==============================================" ++ fnl () ++
          Printer.pr_econstr_env (env gl) (sigma gl) (concl gl));
        tac
      end

    let pr_econstr s c tac =
      let open Goal in
      enter begin fun gl ->
        Feedback.msg_debug Pp.(str s ++ str": " ++ Printer.pr_econstr_env (env gl) (sigma gl) c);
        tac
      end

  end`
