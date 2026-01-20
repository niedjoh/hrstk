import benchexec.tools.template
import benchexec.result as result

class Tool(benchexec.tools.template.BaseTool2):
    """
    Tool info for hrstk.
    """

    REQUIRED_PATHS = ["hrstk"]

    def executable(self, tool_locator):
        return tool_locator.find_executable("hrstk")

    def name(self):
        return "hrstk"

    def determine_result(self, run):
        if not run.output:
            return result.RESULT_ERROR

        first_output_line = run.output[0]
        if "YES" in first_output_line:
            return result.RESULT_TRUE_PROP
        elif "NO" in first_output_line:
            return result.RESULT_FALSE_PROP
        elif "MAYBE" in first_output_line:
            return result.RESULT_UNKNOWN
        else:
            return result.RESULT_ERROR
